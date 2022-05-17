use crate::Options;

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
pub struct ArgIterator<'opts, 'str, I: Iterator<Item = &'str str>> {
    inner: &'opts mut Options<'str, I>,
}

impl<'opts, 'str, I: Iterator<Item = &'str str>> ArgIterator<'opts, 'str, I> {
    pub(crate) fn new(inner: &'opts mut Options<'str, I>) -> Self {
        Self { inner }
    }
}

impl<'opts, 'str, I: Iterator<Item = &'str str>> Iterator for ArgIterator<'opts, 'str, I> {
    type Item = &'str str;

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
pub struct IntoArgs<'str, I: Iterator<Item = &'str str>> {
    positional: Option<&'str str>,
    iter: I,
}

impl<'str, I: Iterator<Item = &'str str>> IntoArgs<'str, I> {
    pub(crate) fn new(positional: Option<&'str str>, iter: I) -> Self {
        Self { positional, iter }
    }
}

impl<'str, I: Iterator<Item = &'str str>> Iterator for IntoArgs<'str, I> {
    type Item = &'str str;

    fn next(&mut self) -> Option<Self::Item> {
        self.positional.take().or_else(|| self.iter.next())
    }
}
