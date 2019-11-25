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
            Opt::Short('e') | Opt::Long("execute") => res.execute = opts.value()?,
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
use std::result::Result as StdResult;

/// An argument parser.
///
/// See the [crate documentation](index.html) for more details.
pub struct Options<'a, S>
where
    S: AsRef<str>,
{
    args: &'a [S],
    /// State information.
    state: RefCell<State<'a>>,
}

#[derive(Default)]
struct State<'a> {
    /// Index in `args`.
    position: usize,
    /// Byte offset in `args[0]`, for parsing multiple short options
    /// in one string.
    index: usize,
    /// Whether we are done parsing options.
    done: bool,
    /// Whether we may get an argument.
    may_get_value: bool,
    /// Whether we must get an argument.
    must_get_value: bool,
    /// Last parsed option.
    last_opt: Option<Opt<'a>>,
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
            state: RefCell::new(State::default()),
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
        let mut state = self.state.borrow_mut();
        if state.done {
            return None;
        }
        if state.position >= self.args.len() {
            state.done = true;
            return None;
        }
        if state.must_get_value {
            return Some(Err(Error::DoesNotRequireValue(state.last_opt.unwrap())));
        }
        let arg = self.args[state.position].as_ref();
        let opt = if state.index == 0 {
            if arg == "--" {
                state.position += 1;
                state.done = true;
                return None;
            } else if arg == "-" {
                state.done = true;
                return None;
            } else if arg.starts_with("--") {
                // Long option
                if let Some(equals) = arg.find('=') {
                    state.index = equals + 1;
                    state.may_get_value = true;
                    state.must_get_value = true;
                    Opt::Long(&arg[2..equals])
                } else {
                    state.position += 1;
                    state.may_get_value = true;
                    Opt::Long(&arg[2..])
                }
            } else if arg.starts_with('-') {
                // Short option
                let ch = arg[1..].chars().next().unwrap();
                state.may_get_value = true;
                state.index = 1 + ch.len_utf8();
                if state.index >= arg.len() {
                    state.position += 1;
                    state.index = 0;
                }
                Opt::Short(ch)
            } else {
                state.done = true;
                return None;
            }
        } else {
            // Another short option in the cluster
            let ch = arg[state.index..].chars().next().unwrap();
            state.may_get_value = true;
            state.index += ch.len_utf8();
            if state.index >= arg.len() {
                state.position += 1;
                state.index = 0;
            }
            Opt::Short(ch)
        };
        state.last_opt = Some(opt);
        Some(Ok(opt))
    }

    /// Retrieve the value passed for this option.
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
    /// assert_eq!(opts.value(), Ok("ay"));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    /// assert_eq!(opts.value(), Ok("foo"));
    /// assert_eq!(opts.next(), Some(Ok(Opt::Short('c'))));
    /// assert_eq!(opts.value(), Ok("see"));
    /// ```
    pub fn value(&self) -> Result<&'a str> {
        let mut state = self.state.borrow_mut();
        if !state.may_get_value || state.position >= self.args.len() {
            if let Some(opt) = state.last_opt {
                return Err(Error::RequiresValue(opt));
            } else {
                panic!("called value() before next()")
            }
        }
        let value = &self.args[state.position].as_ref()[state.index..];
        state.index = 0;
        state.position += 1;
        state.may_get_value = false;
        state.must_get_value = false;
        state.last_opt = None;
        Ok(value)
    }

    /// Retrieves the positional arguments, after the options have
    /// been parsed.
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
        let state = self.state.borrow();
        if !state.done {
            panic!("Option parsing is not complete");
        }
        &self.args[state.position..]
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

impl fmt::Display for Opt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
}

impl fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::UnknownOpt(opt) => write!(f, "unknown option: {}", opt),
            Error::RequiresValue(opt) => write!(f, "option requires a value: {}", opt),
            Error::DoesNotRequireValue(opt) => {
                write!(f, "option does not require a value: {}", opt)
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
        assert_eq!(opts.args(), &["foo", "bar"]);
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
        assert_eq!(opts.args(), &["bar"]);
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
        assert_eq!(opts.args(), &["bar"]);
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
        assert_eq!(opts.args(), &["bar"]);
    }

    #[test]
    fn short_option_with_value() {
        let args = ["-a", "ay", "-b", "bee", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value(), Ok("ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.value(), Ok("bee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["bar"]);
    }

    #[test]
    fn short_cluster_with_value() {
        let args = ["-aay", "-3bbee", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value(), Ok("ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
        assert_eq!(opts.value(), Ok("bee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["bar"]);
    }

    #[test]
    fn long_option_with_value() {
        let args = ["--ay", "Ay", "--bee=Bee", "--see", "See", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.value(), Ok("Ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value(), Ok("Bee"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
        assert_eq!(opts.value(), Ok("See"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["bar"]);
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
        assert_eq!(opts.value(), Ok("-ay"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value(), Ok("--Bee"));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
        assert_eq!(opts.value(), Ok("--See"));
        assert_eq!(opts.next(), Some(Ok(Opt::Short('d'))));
        assert_eq!(opts.value(), Ok("-dee"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["bar"]);
    }

    #[test]
    #[should_panic]
    fn multiple_values() {
        let args = ["-a", "ay", "ay2", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value(), Ok("ay"));
        let _ = opts.value(); // cannot get 2 values
    }

    #[test]
    fn no_positional() {
        let args = ["-a", "ay"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value(), Ok("ay"));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &[] as &[&str]);
    }

    #[test]
    fn long_option_with_empty_value() {
        let args = ["--ay=", "--bee", "", "bar"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
        assert_eq!(opts.value(), Ok(""));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.value(), Ok(""));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["bar"]);
    }

    #[test]
    fn short_option_with_missing_value() {
        let args = ["-a"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Short('a'))));
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
        assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Long("ay"))));
    }

    #[test]
    fn end_of_options() {
        let args = ["-a", "--bee", "--", "--see", "-d"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["--see", "-d"]);
    }

    #[test]
    fn lone_dash() {
        let args = ["-a", "--bee", "-", "--see", "-d"];
        let opts = Options::new(&args);
        assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
        assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
        assert_eq!(opts.next(), None);
        assert_eq!(opts.args(), &["-", "--see", "-d"]);
    }
}
