//! An argument parser that is truly zero-cost, similar to Unix's
//! `getopts`.
//!
//! ## About
//!
//! `getargs` is a low-level, efficient and versatile argument parser
//! that works similarly to `getopts`. It works by producing a stream of
//! options, and after each option, your code decides whether to require
//! and retrieve the value for the option or not.
//!
//! You don't have to declare a list of valid options up-front, so
//! `getargs` does not have to allocate space for them or spend runtime
//! searching for them. This also means that you have to write your own
//! help message, but since `--help` is just another flag, there are no
//! restrictions on what you do with it.
//!
//! ## Features
//!
//! * Short `-f` and long `--flag` flags
//! * Required implicit values `-i VALUE` and `--implicit VALUE`
//! * Required or optional explicit values `-eVALUE` and
//!   `--explicit=VALUE`
//! * Positional arguments and `--`
//!
//! ## Benefits
//!
//! * Zero cost
//! * Zero copy
//! * Zero unsafe code
//! * Zero dependencies
//! * Zero allocation
//! * Simple to use yet versatile
//! * `#![no_std]`-compatible
//! * Compatible with `&str` and `&[u8]`
//!
//! ## Overview
//!
//! - [`Options`] is the main export of the library, and handles
//!   argument parsing. If you don't need a step-by-step tutorial, its
//!   documentation contains everything you need to jump right in.
//!
//! - [`Argument`] is implemented for each type that can be parsed by
//!   [`Options`], such as `&str` and `&[u8]`.
//!
//! - [`Opt`] represents a short or long option, returned by
//!   [`Options::next`].
//!
//! - [`Error`] represents a parsing error.
//!
//! # Tutorial
//!
//! It's easy to parse options using `getargs`.
//!
//! First, obtain an iterator over your arguments as `&str` or `&[u8]`.
//! Usually, this is done by calling [`args()`][std::env::args] or
//! [`args_os()`][std::env::args_os], collecting it into a [`Vec`], and
//! then creating an iterator that uses [`String::as_str`] (or an
//! [`OsString`][std::ffi::OsString] equivalent). On Linux, you can use
//! the [`argv`][argv] crate and [`OsStrExt`][OsStrExt] to get an
//! iterator of `&[u8]` without allocating. On other platforms, `argv`
//! will leak memory, so be careful!
//!
//! Then, pass the iterator to [`Options::new`]. Once you have an
//! [`Options`], you can call [`Options::next`] to get a [`Result`] of
//! an optional [`Opt`]. Don't be scared by `next`'s return type:
//!
//! - The outer [`Result`] is simply for [`Error`]s that occur during
//!   parsing. Right now, only [`Error::DoesNotRequireValue`] can be
//!   returned by [`Options::next`] - but this is an implementation
//!   detail.
//!
//! - The inner [`Option`] is because when a positional argument is
//!   encountered (a non-option that isn't itself a value for one),
//!   there are no more options to parse.
//!
//! Once you have an [`Opt`], you can match on it, and do one of the
//! following things:
//!
//! - Call [`Options::value`], which will tell `getargs` that this
//!   option requires a value, and either return it or raise an
//!   [`Error::RequiresValue`].
//!
//! - Call [`Options::value_opt`], which will tell `getargs` that this
//!   option may have an *optional* value, and return the value, if any.
//!
//! - Do nothing before the next call to [`Options::next`], which will
//!   by default assume that the option should not have had a value (and
//!   raise an [`Error::DoesNotRequireValue`] if an explicit value was
//!   found).
//!
//! You can continue doing this until `next` returns `None`. Once it
//! does, you can call [`Options::arg`] to get positional arguments one
//! by one, [`Options::args`] to get an iterator over positional
//! arguments, or [`Options::into_args`] to turn the [`Options`] into
//! an iterator over the rest of the positional arguments.
//!
//! This pattern lends itself quite well to [`while let`][while let]
//! loops:
//!
//! ```
//! # use getargs::{Options, Opt};
//! # let iter = ["-h", "--help", "-v", "--version"].into_iter();
//! let mut opts = Options::new(iter);
//!
//! while let Some(opt) = opts.next()? {
//!     match opt {
//!         Opt::Short('h') | Opt::Long("help") => { /* ... */ }
//!         Opt::Short('v') | Opt::Long("version") => { /* ... */ }
//!         _ => panic!("Unknown option: {}", opt)
//!     }
//! }
//! # Ok::<(), getargs::Error<&'static str>>(())
//! ```
//!
//! However, [`Options`] notably does not implement [`Iterator`] because
//! a `for` loop borrows the iterator for the duration of the loop,
//! which would make it impossible to call [`Options::value`] and
//! friends.
//!
//! # Examples
//!
//! Here is the full source code of an example (`print`) that prints all
//! the flags and positional arguments it is given:
//!
#![doc = "```"]
#![doc = include_str!("../examples/print.rs")]
#![doc = "```"]
//!
//! First it collects all process arguments as [`String`]s (panicking if
//! they are not valid UTF-8, as per [`args`][std::env::args]), then it
//! creates an [`Options`] from an iterator over the arguments, then it
//! uses a [while let][while let] loop to call [`Options::next`]. Each
//! iteration, it consumes whatever value the option requires (if any).
//!
//! After there are no more options left, it uses [`Options::args`] to
//! iterate over the rest of the arguments as positional.
//!
//! There are other examples available for tasks like reading flags
//! after positional arguments (the `anywhere` examples). Those examples
//! are available on
//! [GitHub](https://github.com/j-tai/getargs/tree/master/examples).
//!
//! [argv]: https://crates.io/crates/argv
//! [OsStrExt]: std::os::unix::ffi::OsStrExt
//! [while let]: https://doc.rust-lang.org/rust-by-example/flow_control/while_let.html

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
/// [`Options`] accepts an iterator of [`Argument`]s and transforms them
/// into [`Opt`]s, their values, and positional arguments.
///
/// - First, create an iterator over your arguments and call
///   [`Options::new`] to create a new [`Options`].
///
/// - You call [`Options::next`] to attempt to parse the next argument
///   as an [`Opt`]. This method can return an [`Error`] if the last
///   option was provided with a value but did not consume it. It can
///   also return `None` if the next argument is not an option.
///
///   Any returned error can be safely ignored and parsing will continue
///   as normal, however, this is not generally recommended.
///
/// - After a call to [`Options::next`] returns an [`Opt`], you *may*
///   call either [`Options::value`] or [`Options::value_opt`] to
///   retrieve the value of the option. In the absence of any call to a
///   value-consuming method, `getargs` assumes the option must not have
///   any value, and will raise that as an error in the next call to
///   [`Options::next`].
///
/// - Once [`Options::next`] returns `Ok(None)`, you *may* call
///   [`Options::opts_ended`] to check if `--` was used. It will never
///   panic.
///
/// - You may call [`Options::arg`], [`Options::args`], or
///   [`Options::into_args`] whenever an option is not currently being
///   parsed. You can call [`Options::value_opt`] to finish the parsing
///   of the current option if the last call to [`Options::next`]
///   returned an option, but be aware that the returned value will not
///   be included in the arguments (due to being a part of the option).
///
/// # Examples
///
/// Here is an idiomatic explainer:
///
/// ```
/// # use getargs::{Options, Opt};
/// #
/// let args = ["--help"];
/// let mut opts = Options::new(args.into_iter());
///
/// while let Some(opt) = opts.next().expect("argument parsing error") {
///     // We now have a call to `Options::value` / `Options::value_str`
///     // to declare whether or not `opt` takes a value. In the absence
///     // of any such call, `getargs` assumes there cannot be a value.
///
///     match opt {
///         Opt::Short('h') | Opt::Long("help") => { /* print help... */ }
///         Opt::Short('v') => { /* print version, or increment verbosity, or... */ }
///         Opt::Short('e') => {
///             // The error for `Options::value` includes the option
///             let value = opts.value().unwrap();
///
///             // do something with value...
///         }
///
///         // `Opt` implements `Display` (if its argument does)
///         _ => panic!("unknown option: {}", opt)
///     }
/// }
///
/// // `Options::opts_ended` could be used here to detect `--`
///
/// // could easily be `while let Some(arg) = opts.arg()`
/// for arg in opts.args() {
///     // do something with each positional argument...
///
///     // If you are concerned about flags being passed here, see the
///     // `anywhere_manual` or `anywhere_helper` examples
/// }
/// ```
///
/// Here are a couple more examples in unit-test format:
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
    /// type [`A`][Argument].
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
    /// `--option=value`, then you should call [`Options::value`] after
    /// receiving the option from this method. Alternatively, you can
    /// call [`Options::value_opt`] instead for optional values.
    ///
    /// Once this method returns `None`, then you should make sure to
    /// use [`Options::arg`] or [`Options::args`] to get the values of
    /// the following positional arguments. See the [`Options`]
    /// documentation for more details.
    ///
    /// If your application accepts positional arguments in between
    /// flags, you can continue to call `next` after each call to
    /// [`Options::arg`] for as long as it returns `Some`. Remember to
    /// check [`Options::opts_ended`] - see the `anywhere_manual` and
    /// `anywhere_helper` examples for implementations of this.
    ///
    /// This method is not an implementation of [`Iterator`] because
    /// `for` loops borrow the iterator for the duration of the loop,
    /// making it impossible to call methods like [`Options::value`].
    /// Instead, use a `while let` loop to iterate over the options.
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
    ///
    /// This flag is not reset by [`Options::arg`].
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Options, Opt};
    /// #
    /// let args = ["-a", "-b", "foo", "-c", "-d", "--", "bar", "-e", "-f"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    /// assert_eq!(opts.next(), Ok(None));
    /// assert_eq!(opts.arg(), Some("foo"));
    ///
    /// // `Options::next` returned `None` because of `foo` (non-option)
    /// assert_eq!(opts.opts_ended(), false);
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('c'))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('d'))));
    /// assert_eq!(opts.next(), Ok(None));
    ///
    /// // `Options::next` returned `None` because of `--`
    /// assert_eq!(opts.opts_ended(), true);
    ///
    /// // Even after an argument is consumed, `opts_ended` remembers
    /// assert_eq!(opts.arg(), Some("bar"));
    /// assert_eq!(opts.opts_ended(), true);
    /// assert_eq!(opts.arg(), Some("-e"));
    /// assert_eq!(opts.arg(), Some("-f"));
    /// assert_eq!(opts.arg(), None);
    ///
    /// // It eventually might forget, but that doesn't matter here
    /// assert_eq!(opts.opts_ended(), false);
    /// ```
    pub fn opts_ended(&self) -> bool {
        matches!(self.state, State::Start { ended_opts: true })
    }

    /// Retrieves the value passed to the option last returned by
    /// [`Options::next`].
    ///
    /// This function returns an error if there is no value to return
    /// because the end of the argument list has been reached.
    ///
    /// # Panics
    ///
    /// This method panics if [`Options::next`] has not yet been called,
    /// if `value` is called twice for the same option, or if the last
    /// call to `next` did not return an option.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["-aay", "--bee=foo", "-c", "see", "bar"];
    /// let mut opts = Options::new(args.into_iter());
    ///
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
    /// [`Options::next`]. Only explicit values are accepted
    /// (`--flag=VALUE`, `-fVALUE`). Implicit values (`--flag VALUE`,
    /// `-f VALUE`) will not be consumed, and they will return `None`.
    ///
    /// The reasoning for this is that if implicit values were consumed
    /// by this method, a subsequent flag could be mistaken as the
    /// value. `--opt=` also needs to be distinct from `--opt` - the
    /// former needs to have an empty value, whereas the latter needs to
    /// have no value.
    ///
    /// Short options do not support empty values.
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
    /// let args = ["--opt=value", "--other-flag", "--opt", "--opt=other", "-o", "-ovalue"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("value"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("other-flag"))));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), None); // does not return "--opt=other"
    /// assert_eq!(opts.next(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("other"));
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('o'))));
    /// assert_eq!(opts.value_opt(), None); // short options can't have empty values
    /// assert_eq!(opts.next(), Ok(Some(Opt::Short('o'))));
    /// assert_eq!(opts.value_opt(), Some("value"));
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
    /// After this method is called, you can parse further options with
    /// [`Options::next`] or continue getting positional arguments
    /// (which will not treat options specially).
    ///
    /// This method preserves the state of [`Options::opts_ended`].
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it can panic if [`Options::next`] has not yet returned
    /// `None` at least once. If [`Options::next`] returns `None`, then
    /// [`Options::arg`] will always be safe to call.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["-a", "foo", "bar"];
    /// let mut opts = Options::new(args.into_iter());
    ///
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

            _ => panic!("called Options::arg() while option parsing hasn't finished"),
        }
    }

    /// Returns an iterator over the positional arguments of this
    /// [`Options`]. The returned iterator will forward
    /// [`Iterator::next`] calls to [`Options::arg`].
    ///
    /// This method does not panic, but [`Iterator::next`] may panic
    /// once it is called if option parsing has not finished
    /// ([`Options::next`] has not returned `Ok(None)`). The exact
    /// requirements are the same as [`Options::arg`].
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

    /// Returns `true` if this [`Options`] has reached the end of its
    /// iterator, and all positional arguments have also been consumed.
    pub fn is_empty(&'_ self) -> bool {
        matches!(self.state, State::End)
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
            _ => panic!("called Options::into_iter() while option parsing hasn't finished"),
        }
    }
}
