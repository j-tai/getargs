use core::iter::Peekable;

use crate::{Argument, Options};

/// An iterator over the positional arguments of an [`Options`].
///
/// For more information, see [`Options::positionals`].
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
/// For more information, see
/// [`Options::into_positionals`][crate::Options::into_positionals].
#[derive(Debug)]
pub struct IntoPositionals<A: Argument, I: Iterator<Item = A>>(Peekable<I>);

impl<A: Argument, I: Iterator<Item = A>> IntoPositionals<A, I> {
    pub(crate) fn new(iter: Peekable<I>) -> Self {
        Self(iter)
    }
}

impl<A: Argument, I: Iterator<Item = A>> Iterator for IntoPositionals<A, I> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}
