/*!
A truly zero-cost argument parser.

# About

`getargs` is a low-level, efficient, and versatile argument parser
that works similarly to "getopts". It works by producing a stream
of options, and after each option, your code decides whether to
require and retrieve the value for the option or not.

You do not have to declare a list of valid options. Therefore, you
write your own help message.

# Basic example

```no_run
use std::process;
use getargs::{Error, Opt, Options, Result};

// You are recommended to create a struct to hold your arguments
#[derive(Default, Debug)]
struct MyArgsStruct<'a> {
    attack_mode: bool,
    em_dashes: bool,
    execute: &'a str,
    set_version: u32,
    positional_args: &'a [String],
}

fn parse_args<'a>(opts: &'a Options<'a, String>) -> Result<MyArgsStruct<'a>> {
    let mut res = MyArgsStruct::default();
    while let Some(opt) = opts.next() {
        match opt? {
            // -a or --attack
            Opt::Short('a') | Opt::Long("attack") => res.attack_mode = true,
            // Unicode short options are supported
            Opt::Short('\u{2014}') => res.em_dashes = true,
            // -e EXPRESSION, or -eEXPRESSION, or
            // --execute EXPRESSION, or --execute=EXPRESSION
            Opt::Short('e') | Opt::Long("execute") => res.execute = opts.value_str()?,
            // Automatically parses the value as a u32
            Opt::Short('V') => res.set_version = opts.value()?,
            // An unknown option was passed
            opt => return Err(Error::UnknownOpt(opt)),
        }
    }
    res.positional_args = opts.args();
    Ok(res)
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let opts = Options::new(&args);
    let options = match parse_args(&opts) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("usage error: {}", e);
            process::exit(1);
        }
    };
    println!("{:#?}", options);
}
```
*/

use std::cell::RefCell;
use std::error::Error as StdError;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::result::Result as StdResult;
use std::str::FromStr;

/// An argument parser.
///
/// See the [crate documentation](index.html) for more details.
pub struct Options<'a, S>
where
    S: AsRef<str>,
{
    args: &'a [S],
    /// State information.
    inner: RefCell<OptionsInner<'a>>,
}

struct OptionsInner<'a> {
    /// Index in `args`.
    position: usize,
    /// The state information.
    state: State<'a>,
}

#[derive(Copy, Clone)]
enum State<'a> {
    /// The starting state. We may not get a value because there is no
    /// previous option. We may get a positional argument or an
    /// option.
    Start,
    /// We have just finished parsing an option, be it short or long,
    /// and we don't know whether the next argument is considered a
    /// value for the option or a positional argument. From here, we
    /// can get the next option, the next value, or the next
    /// positional argument.
    EndOfOption(Opt<'a>),
    /// We are in the middle of a cluster of short options. From here,
    /// we can get the next short option, or we can get the value for
    /// the last short option. We may not get a positional argument.
    ShortOptionCluster(Opt<'a>, usize),
    /// We just consumed a long option with a value attached with `=`,
    /// e.g. `--execute=expression`. We must get the following value.
    LongOptionWithValue(Opt<'a>, usize),
}

impl<'a> State<'a> {
    fn last_opt(&self) -> Opt<'a> {
        match *self {
            State::Start => panic!("called last_opt() on State::Start"),
            State::EndOfOption(opt) => opt,
            State::ShortOptionCluster(opt, _) => opt,
            State::LongOptionWithValue(opt, _) => opt,
        }
    }
}

impl<'a, S> Options<'a, S>
where
    S: AsRef<str>,
{
    /// Creates a new argument parser given the slice of arguments.
    ///
    /// The argument parser only lives as long as the slice of
    /// arguments.
    pub fn new(args: &[S]) -> Options<S> {
        Options {
            args,
            inner: RefCell::new(OptionsInner {
                position: 0,
                state: State::Start,
            }),
        }
    }

    /// Retrieves the next option.
    ///
    /// Returns `None` if there are no more options. Returns
    /// `Some(Err(..))` if a parse error occurs.
    ///
    /// This method mutates the state of the parser (despite taking a
    /// shared reference to self).
    ///
    /// This method does not retrieve any value that goes with the
    /// option. If the option requires an value, such as in
    /// `--option=value`, then you should call
    /// [`value`](#method.value) after getting the option.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Opt, Options};
    /// let args = ["-a", "--bee", "foo"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    /// assert_eq!(opts.next(), None);
    /// ```
    pub fn next(&self) -> Option<Result<Opt<'a>>> {
        let mut inner = self.inner.borrow_mut();
        match inner.state {
            State::Start | State::EndOfOption(_) => {
                if inner.position >= self.args.len() {
                    return None;
                }
                let arg = self.args[inner.position].as_ref();
                if arg == "--" {
                    // End of options
                    inner.position += 1;
                    inner.state = State::Start;
                    None
                } else if arg == "-" {
                    // "-" is a positional argument
                    inner.state = State::Start;
                    None
                } else if arg.starts_with("--") {
                    // Long option
                    if let Some(equals) = arg.find('=') {
                        // Long option with value
                        let opt = Opt::Long(&arg[2..equals]);
                        inner.state = State::LongOptionWithValue(opt, equals + 1);
                        Some(Ok(opt))
                    } else {
                        // Long option without value
                        let opt = Opt::Long(&arg[2..]);
                        inner.position += 1;
                        inner.state = State::EndOfOption(opt);
                        Some(Ok(opt))
                    }
                } else if arg.starts_with("-") {
                    // Short option
                    let ch = arg[1..].chars().next().unwrap();
                    let opt = Opt::Short(ch);
                    let index = 1 + ch.len_utf8();
                    if index >= arg.len() {
                        inner.position += 1;
                        inner.state = State::EndOfOption(opt);
                    } else {
                        inner.state = State::ShortOptionCluster(opt, index);
                    }
                    Some(Ok(opt))
                } else {
                    // Positional argument
                    inner.state = State::Start;
                    None
                }
            }

            State::ShortOptionCluster(_, index) => {
                let arg = self.args[inner.position].as_ref();
                let ch = arg[index..].chars().next().unwrap();
                let opt = Opt::Short(ch);
                let index = index + ch.len_utf8();
                if index >= arg.len() {
                    inner.position += 1;
                    inner.state = State::EndOfOption(opt);
                } else {
                    inner.state = State::ShortOptionCluster(opt, index);
                }
                Some(Ok(opt))
            }

            State::LongOptionWithValue(opt, _) => Some(Err(Error::DoesNotRequireValue(opt))),
        }
    }

    /// Retrieves the value passed for this option as a string.
    ///
    /// This function returns an error if there is no value to return
    /// because the end of the argument list has been reached.
    ///
    /// This function is not pure, and it mutates the state of the
    /// parser (despite taking a shared reference to self).
    ///
    /// # Panics
    ///
    /// This method panics if [`next`](#method.next) has not yet been
    /// called, or it is called twice for the same option.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Opt, Options};
    /// let args = ["-aay", "--bee=foo", "-c", "see", "bar"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// assert_eq!(opts.value_str(), Ok("ay"));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    /// assert_eq!(opts.value_str(), Ok("foo"));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('c'))));
    /// assert_eq!(opts.value_str(), Ok("see"));
    /// ```
    pub fn value_str(&self) -> Result<&'a str> {
        let mut inner = self.inner.borrow_mut();
        match inner.state {
            State::Start => panic!("called value() with no previous option"),
            State::EndOfOption(opt) => {
                if inner.position >= self.args.len() {
                    Err(Error::RequiresValue(opt))
                } else {
                    let val = self.args[inner.position].as_ref();
                    inner.position += 1;
                    inner.state = State::Start;
                    Ok(val)
                }
            }
            State::ShortOptionCluster(_, index) | State::LongOptionWithValue(_, index) => {
                let val = &self.args[inner.position].as_ref()[index..];
                inner.position += 1;
                inner.state = State::Start;
                Ok(val)
            }
        }
    }

    /// Retrieves the value passed for this option and parses it.
    ///
    /// This method retrieves the value passed for the last option and
    /// parses it as any type that implements `FromStr` (and any
    /// potential error is `Display`). It returns an error if there is
    /// no value to return because the end of the argument list has
    /// been reached, or if the value failed to parse.
    ///
    /// This function is not pure, and it mutates the state of the
    /// parser (despite taking a shared reference to self).
    ///
    /// # Panics
    ///
    /// This method panics if [`next`](#method.next) has not yet been
    /// called, or it is called twice for the same option.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Error, Opt, Options, Result};
    /// let args = ["-a1", "--bee=2.5", "-c", "see", "bar"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// let val: Result<i32> = opts.value();
    /// assert_eq!(val, Ok(1));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    /// assert_eq!(opts.value::<f64>(), Ok(2.5));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('c'))));
    /// assert_eq!(opts.value::<i64>(), Err(Error::InvalidValue {
    ///     opt: Opt::Short('c'),
    ///     desc: "invalid digit found in string".to_string(),
    ///     value: "see",
    /// }));
    /// ```
    pub fn value<T>(&self) -> Result<T>
    where
        T: FromStr,
        T::Err: Display,
    {
        let opt = self.inner.borrow().state.last_opt();
        let value = self.value_str()?;
        T::from_str(value).map_err(|e| Error::InvalidValue {
            opt,
            desc: format!("{}", e),
            value,
        })
    }

    /// Retrieves the next positional argument as a string, after the
    /// options have been parsed.
    ///
    /// This method returns the next positional argument after the
    /// parsed options as a string. This method must be called after
    /// the options has finished parsing.
    ///
    /// After this method is called, this struct may be re-used to
    /// parse further options with [`next`](#method.next), or you can
    /// continue getting positional arguments (which will treat
    /// options as regular positional arguments).
    ///
    /// This function is not pure, and it mutates the state of the
    /// parser (despite taking a shared reference to self).
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it panics if [`next`](#method.next) has not yet
    /// returned `None` at least once.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Opt, Options};
    /// let args = ["-a", "foo", "bar"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// assert_eq!(opts.next(), None);
    /// assert_eq!(opts.arg_str(), Some(&"foo"));
    /// assert_eq!(opts.arg_str(), Some(&"bar"));
    /// assert_eq!(opts.arg_str(), None);
    /// ```
    pub fn arg_str(&self) -> Option<&'a S> {
        let mut inner = self.inner.borrow_mut();
        match inner.state {
            State::Start => {
                if inner.position >= self.args.len() {
                    None
                } else {
                    let arg = &self.args[inner.position];
                    inner.position += 1;
                    Some(arg)
                }
            }
            _ => panic!("called arg() while option parsing hasn't finished"),
        }
    }

    /// Retrieves and parses the next positional argument, after the
    /// options have been parsed.
    ///
    /// This method returns the next positional argument after the
    /// parsed options, parsed as any type that implements `FromStr`
    /// (and any potential error is `Display`). This method must be
    /// called after the options has finished parsing.
    ///
    /// After this method is called, this struct may be re-used to
    /// parse further options with [`next`](#method.next), or you can
    /// continue getting positional arguments (which will treat
    /// options as regular positional arguments).
    ///
    /// This function is not pure, and it mutates the state of the
    /// parser (despite taking a shared reference to self).
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it panics if [`next`](#method.next) has not yet
    /// returned `None` at least once.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Error, Opt, Options, Result};
    /// let args = ["-a", "1", "3.5", "foo"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// assert_eq!(opts.next(), None);
    /// let arg: Option<Result<i32>> = opts.arg();
    /// assert_eq!(arg, Some(Ok(1)));
    /// assert_eq!(opts.arg::<f64>(), Some(Ok(3.5)));
    /// assert_eq!(opts.arg::<i32>(), Some(Err(Error::InvalidArg {
    ///     desc: "invalid digit found in string".to_string(),
    ///     value: "foo",
    /// })));
    /// ```
    pub fn arg<T>(&self) -> Option<Result<T>>
    where
        T: FromStr,
        T::Err: Display,
    {
        let arg = self.arg_str()?.as_ref();
        match T::from_str(arg) {
            Ok(v) => Some(Ok(v)),
            Err(e) => Some(Err(Error::InvalidArg {
                desc: format!("{}", e),
                value: arg,
            })),
        }
    }

    /// Retrieves the rest of the positional arguments, after the
    /// options have been parsed.
    ///
    /// This method returns the list of arguments after the parsed
    /// options.
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it panics if [`next`](#method.next) has not yet
    /// returned `None` at least once.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Opt, Options};
    /// let args = ["-a", "foo", "bar"];
    /// let opts = Options::new(&args);
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    /// assert_eq!(opts.next(), None);
    /// assert_eq!(opts.args(), &["foo", "bar"]);
    /// ```
    pub fn args(&self) -> &'a [S] {
        let inner = self.inner.borrow();
        match inner.state {
            State::Start => &self.args[inner.position..],
            _ => panic!("called args() while option parsing hasn't finished"),
        }
    }
}

/// A short or long option.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Opt<'a> {
    /// A short option, as in `-a`.
    Short(char),
    /// A long option, as in `--attack`.
    Long(&'a str),
}

impl Display for Opt<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Opt::Short(c) => write!(f, "-{}", c),
            Opt::Long(s) => write!(f, "--{}", s),
        }
    }
}

// Error handling

/// A parse error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<'a> {
    /// An unknown option was passed.
    UnknownOpt(Opt<'a>),
    /// The option requires a value, but one was not supplied.
    RequiresValue(Opt<'a>),
    /// The option does not require a value, but one was supplied.
    DoesNotRequireValue(Opt<'a>),
    /// A value for an option could not be parsed.
    InvalidValue {
        opt: Opt<'a>,
        desc: String,
        value: &'a str,
    },
    /// A positional argument could not be parsed.
    InvalidArg { desc: String, value: &'a str },
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Error::UnknownOpt(opt) => write!(f, "unknown option: {}", opt),
            Error::RequiresValue(opt) => write!(f, "option requires a value: {}", opt),
            Error::DoesNotRequireValue(opt) => {
                write!(f, "option does not require a value: {}", opt)
            }
            Error::InvalidValue { opt, desc, value } => {
                write!(f, "invalid value for option '{}': {}: {}", opt, desc, value)
            }
            Error::InvalidArg { desc, value } => {
                write!(f, "invalid value for argument: {}: {}", desc, value)
            }
        }
    }
}

impl StdError for Error<'_> {}

pub type Result<'a, T> = StdResult<T, Error<'a>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_options() {
        let args = ["foo", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"foo"));
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn short_options() {
        let args = ["-a", "-b", "-3", "-@", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('@'))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn short_cluster() {
        let args = ["-ab3@", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('@'))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn long_options() {
        let args = ["--ay", "--bee", "--see", "--@3", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("@3"))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn short_option_with_value() {
        let args = ["-a", "ay", "-b", "bee", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Ok("ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.value_str(), Ok("bee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn short_cluster_with_value() {
        let args = ["-aay", "-3bbee", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Ok("ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.value_str(), Ok("bee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn long_option_with_value() {
        let args = ["--ay", "Ay", "--bee=Bee", "--see", "See", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.value_str(), Ok("Ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value_str(), Ok("Bee"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
        assert_eq!(opts.value_str(), Ok("See"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn value_with_dash() {
        let args = [
            "-a",
            "-ay",
            "--bee=--Bee",
            "--see",
            "--See",
            "-d-dee",
            "bar",
        ];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Ok("-ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value_str(), Ok("--Bee"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
        assert_eq!(opts.value_str(), Ok("--See"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('d'))));
        assert_eq!(opts.value_str(), Ok("-dee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    #[should_panic]
    fn multiple_values() {
        let args = ["-a", "ay", "ay2", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Ok("ay"));
        let _ = opts.value_str(); // cannot get 2 values
    }

    #[test]
    fn no_positional() {
        let args = ["-a", "ay"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Ok("ay"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn long_option_with_empty_value() {
        let args = ["--ay=", "--bee", "", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.value_str(), Ok(""));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value_str(), Ok(""));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"bar"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn short_option_with_missing_value() {
        let args = ["-a"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value_str(), Err(Error::RequiresValue(Opt::Short('a'))));
    }

    #[test]
    fn long_option_with_unexpected_value() {
        let args = ["--ay=Ay", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(
            opts.next(),
            Some(Err(Error::DoesNotRequireValue(Opt::Long("ay")))),
        );
    }

    #[test]
    fn long_option_with_missing_value() {
        let args = ["--ay"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.value_str(), Err(Error::RequiresValue(Opt::Long("ay"))));
    }

    #[test]
    fn end_of_options() {
        let args = ["-a", "--bee", "--", "--see", "-d"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"--see"));
        assert_eq!(opts.arg_str(), Some(&"-d"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn lone_dash() {
        let args = ["-a", "--bee", "-", "--see", "-d"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), Some(&"-"));
        assert_eq!(opts.arg_str(), Some(&"--see"));
        assert_eq!(opts.arg_str(), Some(&"-d"));
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn parse_value() {
        let args = ["-a", "3.14", "--bee=5"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value::<f64>(), Ok(3.14));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value::<i32>(), Ok(5));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg_str(), None);
    }

    #[test]
    fn parse_arg() {
        let args = ["-a", "3.14", "5"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.arg::<f64>(), Some(Ok(3.14)));
        assert_eq!(opts.arg::<i32>(), Some(Ok(5)));
        assert_eq!(opts.arg::<i32>(), None);
    }

    #[test]
    fn parse_invalid_value() {
        let args = ["-a", "3.14.1"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(
            opts.value::<f64>(),
            Err(Error::InvalidValue {
                opt: Opt::Short('a'),
                desc: "invalid float literal".to_string(),
                value: "3.14.1",
            })
        );
    }

    #[test]
    fn parse_invalid_arg() {
        let args = ["-a", "3.14.1"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), None);
        assert_eq!(
            opts.arg::<f64>(),
            Some(Err(Error::InvalidArg {
                desc: "invalid float literal".to_string(),
                value: "3.14.1",
            }))
        );
    }
}
