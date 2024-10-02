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
//! * Parse options at the beginning of the argument list, or anywhere
//! * Optionally parse negative numbers as positional arguments
//!
//! ## Benefits
//!
//! * Zero cost
//! * Zero copy
//! * Zero unsafe code except for `&OsStr`
//! * Zero dependencies
//! * Zero allocation
//! * Simple to use yet versatile
//! * `#![no_std]`-compatible
//! * Compatible with `&str`, `&[u8]` and `&OsStr`
//!
//! ## Performance
//!
//! `getargs` has had a lot of attention put into profiling and
//! optimization, and on a modern machine it takes under 0.2μs to parse
//! a short array of 12 arguments.
//!
//! In our testing, `getargs` is faster than every other argument
//! parsing library on crates.io. Its closest competitor is `gumdrop`,
//! which is only ~30% slower in the worst case, and its second-closest
//! competitor is `getopt`, which takes three times as long. Other
//! libraries degrade quickly; `clap` takes 45x longer. (This is not an
//! entirely fair comparison though, as `clap` is not just an
//! argument-parsing library, but an entire command-line application
//! framework. It is perhaps overqualified for simple tasks.)
//!
//! ## Quickstart
//!
//! Check out the [examples].
//!
//! [examples]: https://github.com/j-tai/getargs/tree/master/examples
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
//!   [`Options::next_opt`].
//!
//! - [`Arg`] represents either an option or a positional argument,
//!   returned by [`Options::next_arg`].
//!
//! - [`Error`] represents a parsing error.
//!
//! ## Obtaining an `Options`
//!
//! First, get an iterator over your arguments as `&str` or `&[u8]`.
//! Usually, this is done by using [`args()`][std::env::args] or
//! [`args_os()`][std::env::args_os]:
//!
//! ```
//! let args = std::env::args()
//!     .skip(1) // remember to skip the executable name!
//!     .collect::<Vec<_>>();
//! ```
//!
//! On Linux, you can use the [`argv`] crate and [`OsStrExt`] to get an
//! iterator of `&[u8]` without allocating:
//!
//! ```
//! # use std::os::unix::ffi::OsStrExt;
//! #
//! // As seen in the `no_alloc` example - only works on Linux due to
//! // the use of `OsStrExt::as_bytes`
//! let args = argv::iter().skip(1).map(OsStrExt::as_bytes);
//! ```
//!
//! On other platforms, `argv` will leak memory, so be careful!
//!
//! Then, pass the iterator to [`Options::new`]:
//!
//! ```
//! # use getargs::Options;
//! # let args = std::iter::empty::<&str>();
//! // ...
//! let mut opts = Options::new(args);
//! #
//! # assert_eq!(opts.next_positional(), None);
//! ```
//!
//! ## Accepting options at the start
//!
//! If your command line looks like this, and does not accept options
//! after positional arguments:
//!
//! ```text
//! usage: command [OPTIONS] [ARGS]...
//! ```
//!
//! then you can use [`Options::next_opt`] directly, just like classical
//! `getargs` (before 0.5.0) supported as `next`. The method is meant to
//! be called in a [`while let`] loop, like so:
//!
//! ```
//! # use getargs::{Options, Opt};
//! # let iter = ["-h", "--help", "-v", "--version", "123"].into_iter();
//! // ...
//! let mut opts = Options::new(iter);
//!
//! while let Some(opt) = opts.next_opt()? {
//!     // read on!
//! #     match opt {
//! #         Opt::Short('h') | Opt::Long("help") => { /* ... */ }
//! #         Opt::Short('v') | Opt::Long("version") => { /* ... */ }
//! #         _ => panic!("Unknown option: {}", opt)
//! #     }
//! }
//! # Ok::<(), getargs::Error<'static, &'static str>>(())
//! ```
//!
//! [`Options`] notably does not implement [`Iterator`], because a `for`
//! loop borrows the iterator for the duration of the loop, which would
//! make it impossible to call [`Options::value`] and friends. Interior
//! mutability would make this possible, but it is difficult to find an
//! API design that does not sacrifice performance.
//!
//! After each [`Opt`], you can choose to do one of three things:
//!
//! - Call [`Options::value`], which will declare that the option
//!   requires a value, and return it or [`Error::RequiresValue`].
//!
//! - Call [`Options::value_opt`], which will declare that the option
//!   may have an *optional* value, and return the value, if any.
//!
//! - Do nothing before the next call to `next_opt`, which will assume
//!   that the option should not have a value (and return an
//!   [`Error::DoesNotRequireValue`] if an explicit value is found).
//!
//! [`Options::next_opt`] will return `Ok(None)` when there are no
//! arguments left, or when `--` is encountered. Once that happens, you
//! can iterate over the rest of the arguments as positional:
//!
//! ```
//! # use getargs::{Options, Opt};
//! # let iter = ["-h", "--help", "-v", "--version", "123"].into_iter();
//! // ...
//! let mut opts = Options::new(iter);
//!
//! while let Some(opt) = opts.next_opt()? {
//!     // ...
//! #     match opt {
//! #         Opt::Short('h') | Opt::Long("help") => { /* ... */ }
//! #         Opt::Short('v') | Opt::Long("version") => { /* ... */ }
//! #         _ => panic!("Unknown option: {}", opt)
//! #     }
//! }
//!
//! for positional in opts.positionals() {
//!     // ...
//! }
//!
//! # Ok::<(), getargs::Error<'static, &'static str>>(())
//! ```
//!
//! Here is the `print` example, which shows required and optional
//! values:
//!
#![doc = "```"]
#![doc = include_str!("../examples/print.rs")]
#![doc = "```"]
//!
//! ## Accepting options anywhere
//!
//! `getargs` includes a utility function, [`Options::next_arg`], that
//! can be used to easily accept both options and positional arguments
//! anywhere. This is starting to become the behavior of many modern
//! programs - arguments that do not begin with `-` or `--` are counted
//! as positional, but option parsing still continues.
//!
//! All you have to do is call `next_arg` instead of `next_opt`, and
//! match on [`Arg`] rather than [`Opt`]:
//!
//! ```
//! # use getargs::{Options, Arg};
//! # let iter = ["-h", "--help", "123", "-v", "--version", "456"].into_iter();
//! // ...
//! let mut opts = Options::new(iter);
//!
//! while let Some(arg) = opts.next_arg()? {
//!     // ...
//!     match arg {
//!         Arg::Short('h') | Arg::Long("help") => { /* ... */ }
//!         Arg::Short('v') | Arg::Long("version") => { /* ... */ }
//!         Arg::Positional(positional) => { /* ... */ }
//!         _ => panic!("Unknown option: {}", arg)
//!     }
//! }
//!
//! # Ok::<(), getargs::Error<'static, &'static str>>(())
//! ```
//!
//! [`Arg`] also has some utility methods, like [`Arg::opt`] and
//! [`Arg::positional`].
//!
//! The rest is virtually identical to parsing with `next_opt`.
//!
//! Here is the `anywhere` example, which is similar to `print` but
//! uses `next_arg` instead of `next_opt`:
//!
#![doc = "```"]
#![doc = include_str!("../examples/anywhere.rs")]
#![doc = "```"]
//!
//! # Examples
//!
//! There are other examples available on [GitHub].
//!
//! [`argv`]: https://crates.io/crates/argv
//! [`OsStrExt`]: std::os::unix::ffi::OsStrExt
//! [`while let`]: https://doc.rust-lang.org/rust-by-example/flow_control/while_let.html
//! [GitHub]: https://github.com/j-tai/getargs/tree/master/examples

#![cfg_attr(not(feature = "std"), no_std)]

mod arg;
mod error;
mod iter;
mod opt;
#[cfg(test)]
mod tests;
mod traits;

pub use arg::Arg;
pub use error::{Error, Result};
pub use iter::{IntoPositionals, Positionals};
pub use opt::Opt;
pub use traits::Argument;

/// An argument parser.
///
/// [`Options`] accepts an iterator of [`Argument`]s and transforms them
/// into [`Opt`]s or [`Arg`]s, their values, and positional arguments.
///
/// - First, create an iterator over your arguments and call
///   [`Options::new`] to create a new [`Options`].
///
/// - You call [`Options::next_opt`] or [`Options::next_arg`] to attempt
///   to parse the next argument as an [`Opt`] or [`Arg`] respectively.
///   These methods can return an [`Error`] if the last option was
///   provided with a value but did not consume it. They can also return
///   `Ok(None)` if the next argument is not an option, or if the end of
///   the arguments list has been reached.
///
///   Any returned error can be safely ignored and parsing will continue
///   as normal, however, this is not generally recommended.
///
/// - After a call to `next_*` returns an [`Opt`] (or an
///   [`Arg::Short`]/[`Arg::Long`]), you *may* call either
///   [`Options::value`] or [`Options::value_opt`] to retrieve the value
///   of the option. In the absence of any call to a value-consuming
///   method, `getargs` assumes the option must not have any value, and
///   will raise that as an error in the next call to `next_*`.
///
/// - Once `next_*` returns `Ok(None)`, you *may* call
///   [`Options::opts_ended`] to check if `--` was used. It will never
///   panic.
///
/// - You may call [`Options::next_positional`],
///   [`Options::positionals`], or [`Options::into_positionals`]
///   whenever an option is not currently being parsed. (You can call
///   [`Options::value_opt`] to finish the parsing of the current option
///   if the last call to `next_*` returned an option, but be aware that
///   the returned value will not be included in the arguments due to
///   being a part of the option.)
///
/// See [the crate-level documentation][crate] for a detailed
/// explanation with step-by-step code examples.
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
/// while let Some(opt) = opts.next_opt().expect("argument parsing error") {
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
/// // could easily be `while let Some(arg) = opts.next_positional()`
/// for arg in opts.positionals() {
///     // do something with each positional argument...
///
///     // If you are concerned about flags being passed here, see the
///     // `anywhere` example, which allows flags anywhere
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
/// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
/// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
/// assert_eq!(opts.next_opt(), Ok(None));
///
/// // Don't forget the positional arguments!
/// assert_eq!(opts.next_positional(), Some("foo"));
/// assert_eq!(opts.next_positional(), None);
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
/// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("cupcake"))));
/// assert_eq!(opts.value(), Ok("value"));
/// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
/// assert_eq!(opts.value(), Ok("value2"));
/// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('v'))));
/// assert_eq!(opts.next_opt(), Ok(None));
/// assert_eq!(opts.next_positional(), Some("foo"));
/// assert_eq!(opts.next_positional(), None);
/// ```
///
/// Parsing options anywhere:
///
/// ```
/// # use getargs::{Arg, Options};
/// #
/// let args = ["x", "-r", "hi", "y", "-ohi", "z", "--", "--not-a-flag"];
/// let mut opts = Options::new(args.into_iter());
///
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("x"))));
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('r'))));
/// assert_eq!(opts.value(), Ok("hi"));
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("y"))));
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('o'))));
/// assert_eq!(opts.value_opt(), Some("hi"));
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("z"))));
/// # assert!(!opts.opts_ended());
/// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("--not-a-flag"))));
/// # assert!(opts.opts_ended());
/// assert_eq!(opts.next_arg(), Ok(None));
/// ```
#[derive(Debug, Clone)]
pub struct Options<'opt, A: Argument, I: Iterator<Item = A>> {
    /// Iterator over the arguments.
    iter: I,
    /// State information.
    state: State<'opt, A>,
    /// Parse short option clusters which look like negative numbers as options
    allow_number_sopts: bool,
}

#[derive(Copy, Clone, Debug)]
enum State<'opt, A: Argument> {
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
    EndOfOption(Opt<'opt>),
    /// We are in the middle of a cluster of short options. From here,
    /// we can get the next short option, or we can get the value for
    /// the last short option. We may not get a positional argument.
    ShortOptionCluster(A),
    /// We just consumed a long option with a value attached with `=`,
    /// e.g. `--execute=expression`. We must get the following value.
    LongOptionWithValue(Opt<'opt>, A),
    /// We have received `None` from the iterator and we are refusing to
    /// advance to be polite.
    End { ended_opts: bool },
}

impl<'opt, A: Argument, I: Iterator<Item = A>> Options<'opt, A, I> {
    /// Creates a new [`Options`] given an iterator over arguments of
    /// type [`A`][Argument].
    ///
    /// The argument parser only lives as long as the iterator, but
    /// returns arguments with the same lifetime as whatever the
    /// iterator yields.
    pub fn new(iter: I) -> Options<'opt, A, I> {
        Options {
            iter,
            state: State::Start { ended_opts: false },
            allow_number_sopts: true,
        }
    }

    pub fn allow_number_short_options(&mut self, value: bool) {
        self.allow_number_sopts = value
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
    /// Once this method returns `Ok(None)`, then you should make sure
    /// to use [`Options::next_positional`] or [`Options::positionals`]
    /// to get the values of the following positional arguments. See the
    /// [`Options`] documentation for more details.
    ///
    /// If your application accepts positional arguments in between
    /// flags, you can use [`Options::next_arg`] instead of `next_opt`.
    pub fn next_opt(&mut self) -> Result<'opt, A, Option<Opt<'opt>>>
    where
        A: 'opt,
    {
        match self.state {
            State::Start { .. } | State::EndOfOption(_) => {
                let next = self.iter.next();

                if next.is_none() {
                    self.state = State::End { ended_opts: false };
                    return Ok(None);
                }

                let arg = next.unwrap();

                if arg.ends_opts() {
                    self.state = State::Start { ended_opts: true };
                    Ok(None)
                } else if let Some((name, value)) = arg.parse_long_opt()? {
                    let opt = Opt::Long(name);

                    if let Some(value) = value {
                        self.state = State::LongOptionWithValue(opt, value);
                    } else {
                        self.state = State::EndOfOption(opt);
                    }

                    Ok(Some(opt))
                } else if let Some(cluster) = arg.parse_short_cluster(self.allow_number_sopts) {
                    let (opt, rest) = cluster.consume_short_opt()?;
                    let opt = Opt::Short(opt);

                    if let Some(rest) = rest {
                        self.state = State::ShortOptionCluster(rest);
                    } else {
                        self.state = State::EndOfOption(opt);
                    }

                    Ok(Some(opt))
                } else {
                    self.state = State::Positional(arg);
                    Ok(None)
                }
            }

            State::ShortOptionCluster(rest) => {
                let (opt, rest) = rest.consume_short_opt()?;
                let opt = Opt::Short(opt);

                if let Some(rest) = rest {
                    self.state = State::ShortOptionCluster(rest);
                } else {
                    self.state = State::EndOfOption(opt);
                }

                Ok(Some(opt))
            }

            State::LongOptionWithValue(opt, _) => {
                self.state = State::Start { ended_opts: false };
                Err(Error::DoesNotRequireValue(opt))
            }

            State::Positional(_) | State::End { .. } => Ok(None),
        }
    }

    /// Retrieves the next *argument*. An *argument* is represented by
    /// [`Arg`] and defined as either an option ([`Opt`]) or a
    /// positional argument.
    ///
    /// # Panics
    ///
    /// Panics if [`Options::next_opt`] does.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Arg, Opt, Options};
    /// #
    /// let args = ["--option", "VALUE", "arg", "arg2", "-vvv", "--option", "VALUE", "--", "arg3", "arg4", "--not-an-option"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// // Regular options and values work...
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Long("option"))));
    /// assert_eq!(opts.value(), Ok("VALUE"));
    ///
    /// // Positional arguments afterwards also work...
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("arg"))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("arg2"))));
    ///
    /// // Options after positional arguments also work
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('v'))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('v'))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('v'))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Long("option"))));
    /// assert_eq!(opts.value(), Ok("VALUE"));
    ///
    /// // `--` is recognized and handled correctly
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("arg3"))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("arg4"))));
    /// assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("--not-an-option"))));
    /// assert_eq!(opts.next_arg(), Ok(None));
    /// #
    /// # assert_eq!(opts.is_empty(), true);
    /// ```
    pub fn next_arg(&mut self) -> Result<'opt, A, Option<Arg<'opt, A>>>
    where
        A: 'opt,
    {
        if !self.opts_ended() {
            if let Some(opt) = self.next_opt()? {
                return Ok(Some(opt.into()));
            }
        }

        Ok(self.next_positional().map(Arg::Positional))
    }

    /// Retrieves the value passed to the option last returned by
    /// [`Options::next_opt`] or [`Options::next_arg`].
    ///
    /// This function returns an error if there is no value to return
    /// because the end of the argument list has been reached.
    ///
    /// # Panics
    ///
    /// This method panics if [`Options::next_opt`] or
    /// [`Options::next_arg`] have not yet been called, if `value` is
    /// called twice for the same option, or if the last call to
    /// `next_*` did not return an option.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["-aay", "--bee=foo", "-c", "see", "bar"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.value(), Ok("ay"));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    /// assert_eq!(opts.value(), Ok("foo"));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('c'))));
    /// assert_eq!(opts.value(), Ok("see"));
    /// ```
    pub fn value(&mut self) -> Result<'opt, A, A> {
        match self.state {
            State::Start { .. } | State::Positional(_) | State::End { .. } => {
                panic!("called Options::value() with no previous option")
            }

            State::EndOfOption(opt) => {
                if let Some(val) = self.iter.next() {
                    self.state = State::Start { ended_opts: false };
                    Ok(val)
                } else {
                    self.state = State::End { ended_opts: false };
                    Err(Error::RequiresValue(opt))
                }
            }

            State::ShortOptionCluster(val) => {
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
    /// [`Options::next_opt`] or [`Options::next_arg`]. Only explicit
    /// values are accepted (`--flag=VALUE`, `-fVALUE`). Implicit values
    /// (`--flag VALUE`, `-f VALUE`) will not be consumed, and they will
    /// return `None`.
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
    /// This method panics if [`Options::next_opt`] or
    /// [`Options::next_arg`] have not yet been called, if `value_opt`
    /// is called twice for the same option, or if the last call to
    /// `next_*` did not return an option.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--opt=value", "--other-flag", "--opt", "--opt=other", "-o", "-ovalue"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("value"));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("other-flag"))));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), None); // does not return "--opt=other"
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    /// assert_eq!(opts.value_opt(), Some("other"));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    /// assert_eq!(opts.value_opt(), None); // short options can't have empty values
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    /// assert_eq!(opts.value_opt(), Some("value"));
    /// assert_eq!(opts.next_opt(), Ok(None));
    /// ```
    pub fn value_opt(&mut self) -> Option<A> {
        match self.state {
            State::Start { .. } | State::Positional(_) | State::End { .. } => {
                panic!("called Options::value_opt() with no previous option")
            }

            // If the option had no explicit `=value`, return None
            State::EndOfOption(_) => None,

            State::ShortOptionCluster(val) | State::LongOptionWithValue(_, val) => {
                self.state = State::Start { ended_opts: false };
                Some(val)
            }
        }
    }

    /// Retrieves the next positional argument. This method must be
    /// called after all the last option has been fully parsed. Usually,
    /// this is when [`Options::next_opt`] returns `Ok(None)`, but it
    /// can also be after calling [`Options::value_opt`].
    ///
    /// After this method is called, you can parse further options with
    /// [`Options::next_opt`] or continue getting positional arguments
    /// (which will not treat options specially).
    ///
    /// This method preserves the state of [`Options::opts_ended`].
    ///
    /// # Panics
    ///
    /// This method panics if the option parsing is not yet complete;
    /// that is, it can panic if [`Options::next_opt`] has not yet
    /// returned `None` at least once. If [`Options::next_opt`] returns
    /// `None`, then [`Options::next_positional`] will always be safe to
    /// call.
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
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next_opt(), Ok(None));
    /// assert_eq!(opts.next_positional(), Some("foo"));
    /// assert_eq!(opts.next_positional(), Some("bar"));
    /// assert_eq!(opts.next_positional(), None);
    /// ```
    pub fn next_positional(&mut self) -> Option<A> {
        match self.state {
            State::Start { ended_opts } => self.iter.next().or_else(|| {
                self.state = State::End { ended_opts };
                None
            }),

            State::Positional(arg) => {
                self.state = State::Start { ended_opts: false };
                Some(arg)
            }

            State::End { .. } => None,

            _ => {
                panic!("called Options::next_positional() while option parsing hasn't finished")
            }
        }
    }

    /// Returns an iterator over the positional arguments of this
    /// [`Options`]. The returned iterator will forward
    /// [`Iterator::next`] calls to [`Options::next_positional`].
    ///
    /// This method does not panic, but [`Iterator::next`] may panic
    /// once it is called if option parsing has not finished
    /// ([`Options::next_opt`] has not returned `Ok(None)`). The exact
    /// requirements are the same as [`Options::next_positional`].
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--flag", "one", "two"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    /// assert_eq!(opts.next_opt(), Ok(None));
    ///
    /// let mut args = opts.positionals();
    ///
    /// assert_eq!(args.next(), Some("one"));
    /// assert_eq!(args.next(), Some("two"));
    /// assert_eq!(args.next(), None);
    /// ```
    pub fn positionals(&mut self) -> Positionals<'_, 'opt, A, I> {
        Positionals::new(self)
    }

    /// Consumes this [`Options`], returning an iterator over the rest
    /// of the arguments. The returned iterator wraps the one originally
    /// passed to [`Options::new`].
    ///
    /// # Panics
    ///
    /// Panics if an option is currently being parsed.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Opt, Options};
    /// #
    /// let args = ["--flag", "one", "two"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    /// assert_eq!(opts.next_opt(), Ok(None));
    ///
    /// let mut iter = opts.into_positionals();
    ///
    /// assert_eq!(iter.next(), Some("one"));
    /// assert_eq!(iter.next(), Some("two"));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_positionals(self) -> IntoPositionals<A, I> {
        match self.state {
            State::Start { .. } | State::EndOfOption(_) | State::End { .. } => {
                IntoPositionals::new(None, self.iter)
            }
            State::Positional(positional) => IntoPositionals::new(Some(positional), self.iter),
            _ => {
                panic!("called Options::into_positionals() while option parsing hasn't finished")
            }
        }
    }

    /// Returns `true` if the last call to [`Options::next_opt`]
    /// encountered a `--`. In that case, it will have returned `None`,
    /// but without this method you wouldn't be able to tell whether
    /// that was due to the `--` or simply the next argument being
    /// positional (or not existing).
    ///
    /// This flag is not reset by [`Options::next_positional`].
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::{Options, Opt};
    /// #
    /// let args = ["-a", "-b", "foo", "-c", "-d", "--", "bar", "-e", "-f"];
    /// let mut opts = Options::new(args.into_iter());
    ///
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    /// assert_eq!(opts.next_opt(), Ok(None));
    /// assert_eq!(opts.next_positional(), Some("foo"));
    ///
    /// // `Options::next_opt` returned `None` because of `foo` (non-option)
    /// assert!(!opts.opts_ended());
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('c'))));
    /// assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('d'))));
    /// assert_eq!(opts.next_opt(), Ok(None));
    ///
    /// // `Options::next_opt` returned `None` because of `--`
    /// assert!(opts.opts_ended());
    ///
    /// // Even after an argument is consumed, `opts_ended` remembers
    /// assert_eq!(opts.next_positional(), Some("bar"));
    /// assert!(opts.opts_ended());
    /// assert_eq!(opts.next_positional(), Some("-e"));
    /// assert_eq!(opts.next_positional(), Some("-f"));
    /// assert_eq!(opts.next_positional(), None);
    /// assert!(opts.opts_ended());
    /// ```
    pub fn opts_ended(&self) -> bool {
        matches!(
            self.state,
            State::Start { ended_opts: true } | State::End { ended_opts: true }
        )
    }

    /// Resets [`Options::opts_ended`], causing it to start returning
    /// `false`. This is useful if you have multiple "levels" of options
    /// and are using [`Options::next_arg`] rather than
    /// [`Options::next_opt`] directly.
    ///
    /// # Panics
    ///
    /// This function does not panic. If executed in an invalid state,
    /// it is simply a no-op.
    pub fn reset_opts_ended(&mut self) {
        if let State::Start { ended_opts } | State::End { ended_opts } = &mut self.state {
            *ended_opts = false;
        }
    }

    /// Returns `true` if this [`Options`] has reached the end of its
    /// iterator, and all positional arguments have also been consumed.
    /// This method will always return `true` when
    /// [`Options::next_positional`] does.
    pub fn is_empty(&'_ self) -> bool {
        matches!(self.state, State::End { .. })
    }

    /// "Restarts" options parsing if the iterator has been exhausted
    /// ([`Options::next_positional`] returned `None`). This only
    /// results in any noticeable effect if the iterator is a repeating
    /// iterator; otherwise, the iterator will never produce more
    /// arguments anyway.
    ///
    /// Most iterators, including iterators over arrays, never repeat
    /// their elements. This method isn't very useful unless you know
    /// the exact behavior of the iterator you're using.
    ///
    /// # Panics
    ///
    /// Panics if iteration is not over, as defined by
    /// [`Options::is_empty`].
    pub fn restart(&'_ mut self) {
        match self.state {
            State::End { .. } => {
                self.state = State::Start { ended_opts: false };
            }
            _ => {
                panic!("called Options::restart() during an iteration")
            }
        }
    }
}
