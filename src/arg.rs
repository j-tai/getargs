use crate::{Argument, Opt};
use core::fmt::{Debug, Display, Formatter};

/// An option or positional argument.
///
/// This enum can be returned by calls to
/// [`Options::next_arg`][crate::Options::next_arg] and represents a
/// short or long command-line option name (but not value) like [`Opt`],
/// or a positional argument.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Arg<'str, A: Argument> {
    /// A short option, like `-f`. Does not include the leading `-`.
    Short(char),
    /// A long option, like `--file`. Does not include the leading `--`.
    Long(&'str str),
    /// A positional argument, like `foo.txt`.
    Positional(A),
}

impl<'str, A: Argument> Arg<'str, A> {
    /// Retrieves an equivalent [`Opt`] represented by this [`Arg`], if
    /// it is [`Arg::Short`] or [`Arg::Long`], otherwise `None`.
    pub fn opt(self) -> Option<Opt<'str>> {
        match self {
            Self::Short(short) => Some(Opt::Short(short)),
            Self::Long(long) => Some(Opt::Long(long)),
            _ => None,
        }
    }

    /// Returns the positional [`Argument`] represented by this [`Arg`],
    /// if it is [`Arg::Positional`], otherwise `None`.
    pub fn positional(self) -> Option<A> {
        match self {
            Self::Positional(arg) => Some(arg),
            _ => None,
        }
    }
}

impl<'str, A: Argument> From<Opt<'str>> for Arg<'str, A> {
    fn from(opt: Opt<'str>) -> Self {
        match opt {
            Opt::Short(short) => Self::Short(short),
            Opt::Long(long) => Self::Long(long),
        }
    }
}

impl<A: Argument> From<A> for Arg<'_, A> {
    fn from(arg: A) -> Self {
        Self::Positional(arg)
    }
}

impl<A: Argument> Display for Arg<'_, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Short(short) => write!(f, "-{}", short),
            Self::Long(long) => write!(f, "--{}", long),
            Self::Positional(arg) => arg.display().fmt(f),
        }
    }
}
