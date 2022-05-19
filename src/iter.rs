use crate::{Argument, Options};

/// An iterator over the positional arguments of an [`Options`]. Calls
/// to [`Iterator::next`] will forward to [`Options::arg`]. This
/// iterator can be obtained by calling [`Options::args`].
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
pub struct ArgIterator<'opts, A: Argument, I: Iterator<Item = A>> {
    inner: &'opts mut Options<A, I>,
}

impl<'opts, A: Argument, I: Iterator<Item = A>> ArgIterator<'opts, A, I> {
    pub(crate) fn new(inner: &'opts mut Options<A, I>) -> Self {
        Self { inner }
    }
}

impl<'opts, A: Argument, I: Iterator<Item = A>> Iterator for ArgIterator<'opts, A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.arg()
    }
}

/// An iterator over what used to be the positional arguments of an
/// [`Options`][crate::Options]. This iterator can be obtained by
/// calling [`Options::into_args`][crate::Options::into_args].
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
/// let mut iter = opts.into_args();
///
/// assert_eq!(iter.next(), Some("one"));
/// assert_eq!(iter.next(), Some("two"));
/// assert_eq!(iter.next(), None);
/// ```
pub struct IntoArgs<A: Argument, I: Iterator<Item = A>> {
    positional: Option<A>,
    iter: I,
}

impl<A: Argument, I: Iterator<Item = A>> IntoArgs<A, I> {
    pub(crate) fn new(positional: Option<A>, iter: I) -> Self {
        Self { positional, iter }
    }
}

impl<A: Argument, I: Iterator<Item = A>> Iterator for IntoArgs<A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.positional.take().or_else(|| self.iter.next())
    }
}
