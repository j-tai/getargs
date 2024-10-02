use core::fmt::{Display, Formatter};

use crate::{traits::ConversionError, Argument, Opt};

/// An argument parsing error.
///
/// [`Error`]s can occur during parsing in calls to
/// [`Options::next_opt`][crate::Options::next_opt],
/// [`Options::next_arg`][crate::Options::next_arg], or
/// [`Options::value`][crate::Options::value]. Right now, the only
/// errors that are possible are:
///
/// - When an option requires a value, but one is not given; when
///   [`Options::value`][crate::Options::value] is called and no value
///   is present.
///
/// - When an option does not require a value, but one is given anyway;
///   [`Options::next_opt`][crate::Options::next_opt] or
///   [`Options::next_arg`][crate::Options::next_arg] is called when
///   [`Options::value`][crate::Options::value] and
///   [`Options::value_opt`][crate::Options::value_opt] have both not
///   been.
#[non_exhaustive]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Error<'opt, A: Argument> {
    /// The option requires a value, but one was not supplied.
    ///
    /// This error is returned when a call to
    /// [`Options::value`][crate::Options::value`] does not find any
    /// value to provide.
    RequiresValue(Opt<'opt>),

    /// The option does not require a value, but one was supplied.
    ///
    /// This error is returned when an option is provided a value but
    /// [`Options::next_opt`][crate::Options::next_opt] or
    /// [`Options::next_arg`][crate::Options::next_arg] is called
    /// without the value being consumed.
    DoesNotRequireValue(Opt<'opt>),

    /// The option was not a valid sequence of UTF-8 bytes.
    ConversionError(ConversionError<A>),
}

impl<A: Argument> From<ConversionError<A>> for Error<'_, A> {
    fn from(value: ConversionError<A>) -> Self {
        Self::ConversionError(value)
    }
}

impl<A: Argument> Display for Error<'_, A> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Error::RequiresValue(opt) => write!(f, "option '{}' requires a value", opt),
            Error::DoesNotRequireValue(opt) => {
                write!(f, "option '{}' does not expect a value", opt)
            }

            Error::ConversionError(e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl<A: Argument> std::error::Error for Error<'_, A> {}

pub type Result<'opt, A, T> = core::result::Result<T, Error<'opt, A>>;
