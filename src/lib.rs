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
//!     Getargs(getargs::Error<&'str str>),
//!     #[error("parsing version: {0}")]
//!     VersionParseError(ParseIntError),
//!     #[error("unknown option: {0}")]
//!     UnknownOption(Opt<&'str str>)
//! }
//!
//! impl<'arg> From<getargs::Error<&'arg str>> for Error<'arg> {
//!     fn from(error: getargs::Error<&'arg str>) -> Self {
//!         Self::Getargs(error)
//!     }
//! }
//!
//! // You are recommended to create a struct to hold your arguments
//! #[derive(Default, Debug)]
//! struct MyArgsStruct<'str> {
//!     attack_mode: bool,
//!     em_dashes: bool,
//!     execute: &'str str,
//!     set_version: u32,
//!     positional_args: Vec<&'str str>,
//! }
//!
//! fn parse_args<'a, 'str, I: Iterator<Item = &'str str>>(opts: &'a mut Options<&'str str, I>) -> Result<MyArgsStruct<'str>, Error<'str>> {
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
mod traits;

pub use error::{Error, Result};
pub use iter::{ArgIterator, IntoArgs};
pub use opt::Opt;
pub use traits::Argument;

/// An argument parser.
///
/// See the [crate documentation](index.html) for more details.
#[derive(Copy, Clone, Debug)]
pub struct Options<A: Argument, I: Iterator<Item = A>> {
    /// Iterator over the arguments.
    iter: I,
    /// State information.
    state: State<A>,
}

#[derive(Copy, Clone, Debug)]
enum State<A: Argument> {
    /// The starting state. We may not get a value because there is no
    /// previous option. We may get a positional argument or an
    /// option.
    Start { ended_opts: bool },
    /// We found a positional option and want to preserve it, since it
    /// will no longer be returned from the iterator.
    Positional(A),
    /// We have just finished parsing an option, be it short or long,
    /// and we don't know whether the next argument is considered a
    /// value for the option or a positional argument. From here, we
    /// can get the next option, the next value, or the next
    /// positional argument.
    EndOfOption(Opt<A>),
    /// We are in the middle of a cluster of short options. From here,
    /// we can get the next short option, or we can get the value for
    /// the last short option. We may not get a positional argument.
    ShortOptionCluster(Opt<A>, A),
    /// We just consumed a long option with a value attached with `=`,
    /// e.g. `--execute=expression`. We must get the following value.
    LongOptionWithValue(Opt<A>, A),
    /// We have recieved `None` from the iterator and we are refusing to
    /// advance to be polite.
    End,
}

impl<'arg, A: Argument + 'arg, I: Iterator<Item = A>> Options<A, I> {
    /// Creates a new [`Options`] given an iterator over arguments of
    /// type [`A`].
    ///
    /// The argument parser only lives as long as the iterator, but
    /// returns arguments with the same lifetime as whatever the
    /// iterator yields.
    pub fn new(iter: I) -> Options<A, I> {
        Options {
            iter,
            state: State::Start { ended_opts: false },
        }
    }

    /// Retrieves the next option.
    ///
    /// Returns `Ok(None)` if there are no more options, or `Err(..)` if
    /// a parse error occurs.
    ///
    /// This method also does not retrieve any value that goes with an
    /// option. If the option requires an value, such as in
    /// `--option=value`, then you should call [`value`][Options::value]
    /// after receiving the option from this method. Alternatively, you
    /// can call [`value_opt`][Options::value_opt] for optional values.
    ///
    /// Once this method returns `None`, then you should make sure to
    /// use [`arg`][Options::arg] or [`args`][Options::args] to get the
    /// values of the following positional arguments.
    ///
    /// If your application accepts positional arguments in between
    /// flags (not recommended), you can continue to call `next` after
    /// each call to `arg` for as long as `arg` returns `Some`.
    ///
    /// This method is not an implementation of [`Iterator`] because
    /// `for` loops borrow the iterator for the duration of the loop,
    /// making it impossible to call methods like
    /// [`value`][Options::value]. Instead, use a `while let` loop to
    /// iterate over the options. This is reflected in the examples.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["-a", "--bee", "foo"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    /// assert_eq!(opts.next(), Ok(None));
    ///
    /// // Don't forget the positional arguments!
    /// assert_eq!(opts.arg(), Some("foo"));
    /// assert_eq!(opts.arg(), None);
    /// ```
    ///
    /// Retrieving values from options:
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--cupcake=value", "-b", "value2", "-v", "foo"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("cupcake"))));
    /// assert_eq!(opts.value(), Ok("value"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    /// assert_eq!(opts.value(), Ok("value2"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('v'))));
    /// assert_eq!(opts.next(), Ok(None));
    /// assert_eq!(opts.arg(), Some("foo"));
    /// assert_eq!(opts.arg(), None);
    /// ```
    #[allow(clippy::should_implement_trait)] // `for` loops are not useful here
    pub fn next(&'_ mut self) -> Result<A, Option<Opt<A>>> {
        match self.state {
            State::Start { .. } | State::EndOfOption(_) => {
                let next = self.iter.next();

                if next.is_none() {
                    self.state = State::End;
                    return Ok(None);
                }

                let arg = next.unwrap();

                if arg.ends_opts() {
                    self.state = State::Start { ended_opts: true };
                    Ok(None)
                } else if let Some((name, value)) = arg.parse_long_opt() {
                    let opt = Opt::Long(name);

                    if let Some(value) = value {
                        self.state = State::LongOptionWithValue(opt, value);
                    } else {
                        self.state = State::EndOfOption(opt);
                    }

                    Ok(Some(opt))
                } else if let Some(cluster) = arg.parse_short_cluster() {
                    let (opt, rest) = cluster.consume_short_opt();
                    let opt = Opt::Short(opt);

                    if let Some(rest) = rest {
                        self.state = State::ShortOptionCluster(opt, rest);
                    } else {
                        self.state = State::EndOfOption(opt);
                    }

                    Ok(Some(opt))
                } else {
                    // Positional argument
                    self.state = State::Positional(arg);
                    Ok(None)
                }
            }

            State::ShortOptionCluster(_, rest) => {
                let (opt, rest) = rest.consume_short_opt();
                let opt = Opt::Short(opt);

                if let Some(rest) = rest {
                    self.state = State::ShortOptionCluster(opt, rest);
                } else {
                    self.state = State::EndOfOption(opt);
                }

                Ok(Some(opt))
            }

            State::LongOptionWithValue(opt, _) => {
                self.state = State::Start { ended_opts: false };
                Err(Error::DoesNotRequireValue(opt))
            }

            State::Positional(_) | State::End => Ok(None),
        }
    }

    /// Returns `true` if the last call to [`Options::next`] encountered
    /// a `--`. In that case, it will have returned `None`, but without
    /// this method you wouldn't be able to tell whether that was due to
    /// the `--` or simply the next argument being positional (or not
    /// existing).
    pub fn opts_ended(&self) -> bool {
        matches!(self.state, State::Start { ended_opts: true })
    }

    /// Retrieves the value passed to the option last returned by
    /// [`next`][Options::next].
    ///
    /// This function returns an error if there is no value to return
    /// because the end of the argument list has been reached.
    ///
    /// # Panics
    ///
    /// This method panics if [`next`][Options::next] has not yet been
    /// called, if `value` is called twice for the same option, or if
    /// the last call to `next` did not return an option.
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
    pub fn value(&'_ mut self) -> Result<A, A> {
        match self.state {
            State::Start { .. } | State::Positional(_) | State::End => {
                panic!("called Options::value() with no previous option")
            }

            State::EndOfOption(opt) => {
                if let Some(val) = self.iter.next() {
                    self.state = State::Start { ended_opts: false };
                    Ok(val)
                } else {
                    self.state = State::End;
                    Err(Error::RequiresValue(opt))
                }
            }

            State::ShortOptionCluster(_, val) => {
                self.state = State::Start { ended_opts: false };
                Ok(val.consume_short_val())
            }

            State::LongOptionWithValue(_, val) => {
                self.state = State::Start { ended_opts: false };
                Ok(val)
            }
        }
    }

    /// Retrieves an *optional* value for the option last returned by
    /// [`next`][Options::next]. Only explicit values are accepted
    /// (`--flag=VALUE`, `-fVALUE`). Implicit values (`--flag VALUE`,
    /// `-f VALUE`) will not be consumed, and they will return `None`.
    ///
    /// If implicit values were to be parsed by this function, a
    /// subsequent flag could be mistaken as the value. `--flag=` also
    /// needs to be distinct from `--flag` - the former has an empty
    /// value, whereas the latter has no value, and will not attempt to
    /// consume the next argument.
    ///
    /// # Panics
    ///
    /// This method panics if [`Options::next`] has not yet been called,
    /// if `value_opt` is called twice for the same option, or if the
    /// last call to `next` did not return an option.
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
    pub fn value_opt(&'_ mut self) -> Option<A> {
        match self.state {
            State::Start { .. } | State::Positional(_) | State::End => {
                panic!("called Options::value_opt() with no previous option")
            }

            // If the option had no explicit `=value`, return None
            State::EndOfOption(_) => None,

            State::ShortOptionCluster(_, val) | State::LongOptionWithValue(_, val) => {
                self.state = State::Start { ended_opts: false };
                Some(val)
            }
        }
    }

    /// Retrieves the next positional argument. This method must be
    /// called after all available options have been parsed.
    ///
    /// After this method is called, this struct may be re-used to
    /// parse further options with [`next`][Options::next], or you can
    /// continue getting positional arguments (which will treat
    /// options as regular positional arguments).
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it panics if [`next`][Options::next] has not yet
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
    pub fn arg(&'_ mut self) -> Option<A> {
        match self.state {
            State::Start { .. } => self.iter.next().or_else(|| {
                self.state = State::End;
                None
            }),

            State::Positional(arg) => {
                self.state = State::Start { ended_opts: false };
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
    pub fn args(&mut self) -> ArgIterator<A, I> {
        ArgIterator::new(self)
    }

    /// "Restarts" options parsing if the iterator has been exhausted
    /// ([`Options::arg`] returned `None`). This only results in any
    /// noticeable effect if the iterator is a repeating iterator;
    /// otherwise, the iterator will never produce more arguments
    /// anyway.
    ///
    /// Most iterators, including iterators over arrays, never repeat
    /// their elements. This method isn't very useful unless you know
    /// the exact behavior of the iterator you're using.
    pub fn restart(&'_ mut self) {
        self.state = match self.state {
            State::End => State::Start { ended_opts: false },
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
    pub fn into_args(self) -> IntoArgs<A, I> {
        match self.state {
            State::Start { .. } | State::EndOfOption(_) | State::End => {
                IntoArgs::new(None, self.iter)
            }
            State::Positional(positional) => IntoArgs::new(Some(positional), self.iter),
            _ => panic!("called Options::into_iter() while an option's parsing hasn't finished"),
        }
    }
}
