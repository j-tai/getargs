use core::fmt::{Display, Formatter};

use crate::Opt;

/// A parse error.
#[non_exhaustive]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Error<'str> {
    /// The option requires a value, but one was not supplied.
    RequiresValue(Opt<'str>),
    /// The option does not require a value, but one was supplied.
    DoesNotRequireValue(Opt<'str>),
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Error::RequiresValue(opt) => write!(f, "option requires a value: {}", opt),

            Error::DoesNotRequireValue(opt) => {
                write!(f, "option does not require a value: {}", opt)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error<'_> {}

pub type Result<'a, T> = core::result::Result<T, Error<'a>>;
