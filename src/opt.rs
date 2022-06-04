use core::fmt::{Display, Formatter};

use crate::{Arg, Argument};

/// A short or long option.
///
/// This enum can be returned by calls to
/// [`Options::next_opt`][crate::Options::next_opt] and represents a
/// short or long command-line option name (but not value).
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum Opt<A: Argument> {
    /// A short option, like `-f`. Does not include the leading `-`.
    Short(A::ShortOpt),
    /// A long option, like `--file`. Does not include the leading `--`.
    Long(A),
}

impl<A: Argument> TryFrom<Arg<A>> for Opt<A> {
    type Error = ();

    fn try_from(value: Arg<A>) -> Result<Self, Self::Error> {
        match value {
            Arg::Short(short) => Ok(Self::Short(short)),
            Arg::Long(long) => Ok(Self::Long(long)),
            _ => Err(()),
        }
    }
}

impl<S: Display, A: Argument<ShortOpt = S> + Display> Display for Opt<A> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Opt::Short(c) => write!(f, "-{}", c),
            Opt::Long(s) => write!(f, "--{}", s),
        }
    }
}
