use crate::{Argument, Options};

/// An iterator over the positional arguments of an [`Options`].
///
/// For more information, see [`Options::positionals`].
#[derive(Debug)]
pub struct Positionals<'opts, 'opt, A: Argument, I: Iterator<Item = A>> {
    inner: &'opts mut Options<'opt, A, I>,
}

impl<'opts, 'opt, A: Argument, I: Iterator<Item = A>> Positionals<'opts, 'opt, A, I> {
    pub(crate) fn new(inner: &'opts mut Options<'opt, A, I>) -> Self {
        Self { inner }
    }
}

impl<'opts, 'opt, A: Argument, I: Iterator<Item = A>> Iterator for Positionals<'opts, 'opt, A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_positional()
    }
}

/// An iterator over what used to be the positional arguments of an
/// [`Options`][crate::Options].
///
/// For more information, see
/// [`Options::into_positionals`][crate::Options::into_positionals].
#[derive(Debug, Clone)]
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
