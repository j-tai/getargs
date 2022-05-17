//! A truly zero-cost argument parser.
//!
//! # About
//!
//! `getargs` is a low-level, efficient, and versatile argument parser
//! that works similarly to "getopts". It works by producing a stream
//! of options, and after each option, your code decides whether to
//! require and retrieve the value for the option or not.
//!
//! You do not have to declare a list of valid options. Therefore, you
//! write your own help message.
//!
//! # Basic example
//!
//! ```no_run
//! use std::process;
//! use getargs::{Opt, Options};
//! use std::str::FromStr;
//! use std::num::ParseIntError;
//!
//! #[derive(Clone, Eq, PartialEq, Debug, thiserror::Error)]
//! enum Error<'str> {
//!     #[error("{0:?}")]
//!     Getargs(getargs::Error<'str>),
//!     #[error("parsing version: {0}")]
//!     VersionParseError(ParseIntError),
//!     #[error("unknown option: {0}")]
//!     UnknownOption(Opt<'str>)
//! }
//!
//! impl<'str> From<getargs::Error<'str>> for Error<'str> {
//!     fn from(error: getargs::Error<'str>) -> Self {
//!         Self::Getargs(error)
//!     }
//! }
//!
//! // You are recommended to create a struct to hold your arguments
//! #[derive(Default, Debug)]
//! struct MyArgsStruct<'a> {
//!     attack_mode: bool,
//!     em_dashes: bool,
//!     execute: &'a str,
//!     set_version: u32,
//!     positional_args: Vec<&'a str>,
//! }
//!
//! fn parse_args<'a, 'str, I: Iterator<Item = &'str str>>(opts: &'a mut Options<'str, I>) -> Result<MyArgsStruct<'str>, Error<'str>> {
//!     let mut res = MyArgsStruct::default();
//!     while let Some(opt) = opts.next()? {
//!         match opt {
//!             // -a or --attack
//!             Opt::Short('a') | Opt::Long("attack") => res.attack_mode = true,
//!             // Unicode short options are supported
//!             Opt::Short('\u{2014}') => res.em_dashes = true,
//!             // -e EXPRESSION, or -eEXPRESSION, or
//!             // --execute EXPRESSION, or --execute=EXPRESSION
//!             Opt::Short('e') | Opt::Long("execute") => res.execute = opts.value()?,
//!             // Automatically parses the value as a u32
//!             Opt::Short('V') => res.set_version = u32::from_str(opts.value()?).map_err(Error::VersionParseError)?,
//!             // An unknown option was passed
//!             opt => return Err(Error::UnknownOption(opt)),
//!         }
//!     }
//!     res.positional_args = opts.args().collect();
//!     Ok(res)
//! }
//!
//! fn main() {
//!     let args: Vec<_> = std::env::args().skip(1).collect();
//!     let mut opts = Options::new(args.iter().map(String::as_str));
//!     let options = match parse_args(&mut opts) {
//!         Ok(o) => o,
//!         Err(e) => {
//!             eprintln!("error: {}", e);
//!             process::exit(1);
//!         }
//!     };
//!     println!("{:#?}", options);
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

mod error;
mod iter;
mod opt;
#[cfg(test)]
mod tests;

pub use error::{Error, Result};
pub use iter::{ArgIterator, IntoArgs};
pub use opt::Opt;

/// An argument parser.
///
/// See the [crate documentation](index.html) for more details.
pub struct Options<'str, I>
where
    I: Iterator<Item = &'str str>,
{
    /// Iterator over the arguments.
    iter: I,
    /// State information.
    state: State<'str>,
}

#[derive(Copy, Clone, Debug)]
enum State<'str> {
    /// The starting state. We may not get a value because there is no
    /// previous option. We may get a positional argument or an
    /// option.
    Start,
    /// We found a positional option and want to preserve it, since it
    /// will no longer be returned from the iterator.
    Positional(&'str str),
    /// We have just finished parsing an option, be it short or long,
    /// and we don't know whether the next argument is considered a
    /// value for the option or a positional argument. From here, we
    /// can get the next option, the next value, or the next
    /// positional argument.
    EndOfOption(Opt<'str>),
    /// We are in the middle of a cluster of short options. From here,
    /// we can get the next short option, or we can get the value for
    /// the last short option. We may not get a positional argument.
    ShortOptionCluster(Opt<'str>, &'str str),
    /// We just consumed a long option with a value attached with `=`,
    /// e.g. `--execute=expression`. We must get the following value.
    LongOptionWithValue(Opt<'str>, &'str str),
    /// We have recieved `None` from the iterator and we are refusing to
    /// advance to be polite.
    End,
}

impl<'str, I> Options<'str, I>
where
    I: Iterator<Item = &'str str>,
{
    /// Creates a new argument parser given an arguments iterator.
    ///
    /// The argument parser only lives as long as the iterator,
    /// but returns strings with the same lifetime as whatever the
    /// iterator yields.
    pub fn new(iter: I) -> Options<'str, I> {
        Options {
            iter,
            state: State::Start,
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
    /// `--option=value`, then you should call [`value`] after
    /// getting the option.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use getargs::{Opt, Options};
    /// let args = ["-a", "--bee", "foo"];
    /// let mut opts = Options::new(args.into_iter());
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    /// assert_eq!(opts.next(), Ok(None));
    /// ```
    #[allow(clippy::should_implement_trait)] // `for` loops are not useful here
    pub fn next(&'_ mut self) -> Result<'str, Option<Opt<'str>>> {
        match self.state {
            State::Start | State::EndOfOption(_) => {
                let next = self.iter.next();
                if next.is_none() {
                    self.state = State::End;
                    return Ok(None);
                }
                let arg = next.unwrap();
                if arg == "--" {
                    // End of options
                    self.state = State::Start;
                    Ok(None)
                } else if arg == "-" {
                    // "-" is a positional argument
                    self.state = State::Positional(arg);
                    Ok(None)
                } else if let Some(flag) = arg.strip_prefix("--") {
                    // Long option
                    if let Some((flag, value)) = flag.split_once('=') {
                        // Long option with value
                        let opt = Opt::Long(flag);
                        self.state = State::LongOptionWithValue(opt, value);
                        Ok(Some(opt))
                    } else {
                        // Long option without value
                        let opt = Opt::Long(flag);
                        self.state = State::EndOfOption(opt);
                        Ok(Some(opt))
                    }
                } else if let Some(chars) = arg.strip_prefix('-') {
                    // Short option
                    let ch = chars.chars().next().unwrap();
                    let opt = Opt::Short(ch);
                    let rest = &chars[ch.len_utf8()..];
                    if rest.is_empty() {
                        self.state = State::EndOfOption(opt);
                    } else {
                        self.state = State::ShortOptionCluster(opt, rest)
                    }
                    Ok(Some(opt))
                } else {
                    // Positional argument
                    self.state = State::Positional(arg);
                    Ok(None)
                }
            }

            State::ShortOptionCluster(_, rest) => {
                let ch = rest.chars().next().unwrap();
                let opt = Opt::Short(ch);
                let rest = &rest[ch.len_utf8()..];
                if rest.is_empty() {
                    self.state = State::EndOfOption(opt);
                } else {
                    self.state = State::ShortOptionCluster(opt, rest);
                }
                Ok(Some(opt))
            }

            State::LongOptionWithValue(opt, _) => Err(Error::DoesNotRequireValue(opt)),

            State::Positional(_) | State::End => Ok(None),
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
    /// let mut opts = Options::new(args.into_iter());
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.value(), Ok("ay"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    /// assert_eq!(opts.value(), Ok("foo"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('c'))));
    /// assert_eq!(opts.value(), Ok("see"));
    /// ```
    pub fn value(&'_ mut self) -> Result<'str, &'str str> {
        match self.state {
            State::Start | State::Positional(_) | State::End => {
                panic!("called Options::value() with no previous option")
            }

            State::EndOfOption(opt) => {
                if let Some(val) = self.iter.next() {
                    self.state = State::Start;
                    Ok(val)
                } else {
                    self.state = State::End;
                    Err(Error::RequiresValue(opt))
                }
            }

            State::ShortOptionCluster(_, val) | State::LongOptionWithValue(_, val) => {
                self.state = State::Start;
                Ok(val)
            }
        }
    }

    /// Retrieves an *optional* value for the current option as a
    /// string. Only explicit values are accepted (`--flag=value`,
    /// `-fVALUE`), and implicit values (`--flag value`, `-f VALUE`)
    /// will simply return `None`.
    ///
    /// This is because a subsequent flag could be interpreted as a
    /// value if it follows a flag with an optional value, and `--flag=`
    /// is distinct from `--flag`.
    ///
    /// # Panics
    ///
    /// This method panics if [`Options::next`] has not yet been called,
    /// or if it is called twice for the same option.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--opt=value", "--other-flag", "--opt", "--opt=other"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("value"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("other-flag"))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), None); // does not return "--opt=other"
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("other"));
    /// assert_eq!(opts.next(), Ok(None));
    /// ```
    pub fn value_opt(&'_ mut self) -> Option<&'str str> {
        match self.state {
            State::Start | State::Positional(_) | State::End => {
                panic!("called Options::value_opt() with no previous option")
            }

            // If the option had no explicit `=value`, return None
            State::EndOfOption(_) => None,

            State::ShortOptionCluster(_, val) | State::LongOptionWithValue(_, val) => {
                self.state = State::Start;
                Some(val)
            }
        }
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
    /// let mut opts = Options::new(args.into_iter());
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next(), Ok(None));
    /// assert_eq!(opts.arg(), Some("foo"));
    /// assert_eq!(opts.arg(), Some("bar"));
    /// assert_eq!(opts.arg(), None);
    /// ```
    pub fn arg(&'_ mut self) -> Option<&'str str> {
        match self.state {
            State::Start => self.iter.next().or_else(|| {
                self.state = State::End;
                None
            }),
            State::Positional(arg) => {
                self.state = State::Start;
                Some(arg)
            }
            State::End => None,

            _ => panic!("called arg() while option parsing hasn't finished"),
        }
    }

    /// Returns an iterator over the positional arguments of this
    /// [`Options`]. The returned iterator will forward
    /// [`Iterator::next`] calls to [`Options::arg`].
    ///
    /// This method does not panic, but [`Iterator::next`] may panic
    /// once it is called if option parsing has not finished
    /// ([`Options::next`] has not returned `Ok(None)`).
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--flag", "one", "two"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("flag"))));
    /// assert_eq!(opts.next(), Ok(None));
    ///
    /// let mut args = opts.args();
    ///
    /// assert_eq!(args.next(), Some("one"));
    /// assert_eq!(args.next(), Some("two"));
    /// assert_eq!(args.next(), None);
    /// ```
    pub fn args<'opts>(&'opts mut self) -> ArgIterator<'opts, 'str, I> {
        ArgIterator::new(self)
    }

    /// "Restarts" options parsing if the iterator has been exhausted.
    /// This only results in any noticeable effect if the iterator is a
    /// repeating iterator; otherwise, nothing happens.
    ///
    /// A "repeating iterator" is one that starts to produce elements
    /// again even after a call to [`Iterator::next`] returns `None`.
    pub fn restart(&'_ mut self) {
        self.state = match self.state {
            State::End => State::Start,
            _ => panic!("called Options::restart() during an iteration"),
        }
    }

    /// Consumes this [`Options`], returning an iterator over the rest
    /// of the arguments. The returned iterator wraps the one originally
    /// passed to [`Options::new`].
    ///
    /// # Panics
    ///
    /// Panics if an option is currently being parsed.
    pub fn into_args(self) -> IntoArgs<'str, I> {
        match self.state {
            State::Start | State::EndOfOption(_) | State::End => IntoArgs::new(None, self.iter),
            State::Positional(positional) => IntoArgs::new(Some(positional), self.iter),
            _ => panic!("called Options::into_iter() while an option's parsing hasn't finished"),
        }
    }
}
