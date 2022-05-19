use core::fmt::{Display, Formatter};

use crate::{Argument, Opt};

/// A parse error.
#[non_exhaustive]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Error<A: Argument> {
    /// The option requires a value, but one was not supplied.
    RequiresValue(Opt<A>),
    /// The option does not require a value, but one was supplied.
    DoesNotRequireValue(Opt<A>),
}

impl<'arg, S: Display, A: Argument<ShortOpt = S> + Display + 'arg> Display for Error<A> {
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
impl<'arg, S: Display, A: Argument<ShortOpt = S> + Display + 'arg> std::error::Error for Error<A> {}

pub type Result<A, T> = core::result::Result<T, Error<A>>;
