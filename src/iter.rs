use crate::{Argument, Options};

/// An iterator over the positional arguments of an [`Options`].
///
/// Calls to [`Iterator::next`] will forward to
/// [`Options::next_positional`]. This iterator can be obtained by
/// calling [`Options::positionals`].
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
#[derive(Debug)]
pub struct Positionals<'opts, A: Argument, I: Iterator<Item = A>> {
    inner: &'opts mut Options<A, I>,
}

impl<'opts, A: Argument, I: Iterator<Item = A>> Positionals<'opts, A, I> {
    pub(crate) fn new(inner: &'opts mut Options<A, I>) -> Self {
        Self { inner }
    }
}

impl<'opts, A: Argument, I: Iterator<Item = A>> Iterator for Positionals<'opts, A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_positional()
    }
}

/// An iterator over what used to be the positional arguments of an
/// [`Options`][crate::Options].
///
/// This iterator can be obtained by calling
/// [`Options::into_positionals`][crate::Options::into_positionals].
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
#[derive(Copy, Clone, Debug)]
pub struct IntoPositionals<A: Argument, I: Iterator<Item = A>> {
    positional: Option<A>,
    iter: I,
}

impl<A: Argument, I: Iterator<Item = A>> IntoPositionals<A, I> {
    pub(crate) fn new(positional: Option<A>, iter: I) -> Self {
        Self { positional, iter }
    }
}

impl<A: Argument, I: Iterator<Item = A>> Iterator for IntoPositionals<A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.positional.take().or_else(|| self.iter.next())
    }
}
