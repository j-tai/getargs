use core::fmt::{Display, Formatter};

/// A short or long option.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Opt<'str> {
    /// A short option, as in `-a`.
    Short(char),
    /// A long option, as in `--attack`.
    Long(&'str str),
}

impl<'str> Display for Opt<'str> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Opt::Short(c) => write!(f, "-{}", c),
            Opt::Long(s) => write!(f, "--{}", s),
        }
    }
}

impl From<char> for Opt<'_> {
    fn from(ch: char) -> Self {
        Self::Short(ch)
    }
}

impl<'str> From<&'str str> for Opt<'str> {
    fn from(s: &'str str) -> Self {
        Self::Long(s)
    }
}
