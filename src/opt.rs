use core::fmt::{Display, Formatter};

use crate::Argument;

/// A short or long option.
///
/// This struct can be returned by calls to
/// [`Options::next`][crate::Options::next] and represents a short or
/// long command-line option name (but not value).
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum Opt<A: Argument> {
    /// A short option, as in `-a`. Does not include the leading `-`.
    Short(A::ShortOpt),
    /// A long option, as in `--attack`. Does not include the leading
    /// `--`.
    Long(A),
}

impl<S: Display, A: Argument<ShortOpt = S> + Display> Display for Opt<A> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Opt::Short(c) => write!(f, "-{}", c),
            Opt::Long(s) => write!(f, "--{}", s),
        }
    }
}
