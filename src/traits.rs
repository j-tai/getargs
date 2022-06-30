use core::fmt::Debug;

/// The argument trait for types that can be parsed by
/// [`Options`][crate::Options].
///
/// This trait is implemented for both [`&str`] and [`&[u8]`][slice],
/// and allows them to be understood by `getargs` enough to parse them -
/// `getargs` is entirely generic over the type of its arguments.
///
/// Adding `#[inline]` to implementations of this trait can improve
/// performance by up to 50% in release mode. This is because `Options`
/// is so blazingly fast (nanoseconds) that the overhead of function
/// calls becomes quite significant. `rustc` should be able to apply
/// this optimization automatically, but doesn't for some reason.
///
/// This trait should not need to be implemented unless you are using
/// arguments that cannot be coerced into `&str` or `&[u8]` for whatever
/// reason. If they can be in any way, you should use an
/// [`Iterator::map`] instead of implementing [`Argument`].
///
/// Implementing `Argument` requires [`Copy`], [`Eq`], and [`Debug`]
/// because it simplifies `#[derive]`s on `getargs`' side and codifies
/// the inexpensive, zero-copy expectations of argument types. This
/// should be a borrow like `&str`, not an owned struct like `String`.
pub trait Argument: Copy + Eq + Debug {
    /// The short-flag type. For [`&str`], this is [`char`]. For
    /// [`&[u8]`][slice], this is `u8`.
    type ShortOpt: Copy + Eq + Debug;

    /// Returns `true` if this argument signals that no additional
    /// options should be parsed. If this method returns `true`, then
    /// [`Options::next_opt`][crate::Options::next_opt] will not attempt
    /// to parse it as one ([`parse_long_opt`][Self::parse_long_opt] and
    /// [`parse_short_cluster`][Self::parse_short_cluster] will not be
    /// called).
    ///
    /// This method should only return `true` if [`Self`] is equal to
    /// the string `"--"` (or equivalent in your datatype). It should
    /// not return `true` if [`Self`] merely *starts* with `"--"`, as
    /// that signals a [long option][Self::parse_long_opt].
    fn ends_opts(self) -> bool;

    /// Attempts to parse this argument as a long option. Returns the
    /// result of the parsing operation, with the leading `--` stripped.
    ///
    /// A long option is defined as an argument that follows the pattern
    /// `--flag` or `--flag=VALUE`, where `VALUE` may be empty.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::Argument;
    /// assert_eq!("--flag".parse_long_opt(), Some(("flag", None)));
    /// assert_eq!("--flag=value".parse_long_opt(), Some(("flag", Some("value"))));
    /// assert_eq!("--flag=".parse_long_opt(), Some(("flag", Some(""))));
    /// assert_eq!("-a".parse_long_opt(), None);
    /// ```
    fn parse_long_opt(self) -> Option<(Self, Option<Self>)>;

    /// Attempts to parse this argument as a "short option cluster".
    /// Returns the short option cluster if present.
    ///
    /// A "short option cluster" is defined as any [`Self`] such that
    /// either at least one [`ShortOpt`][Self::ShortOpt] can be
    /// extracted from it using
    /// [`consume_short_opt`][Self::consume_short_opt], or it can be
    /// converted to a value for a preceding short option using
    /// [`consume_short_val`][Self::consume_short_val].
    ///
    /// A short option cluster is signaled by the presence of a leading
    /// `-` in an argument, and does not include the leading `-`. The
    /// returned "short option cluster" must be valid for at least one
    /// [`consume_short_opt`][Self::consume_short_opt] or
    /// [`consume_short_val`][Self::consume_short_val].
    ///
    /// This method does not need to guard against `--` long options.
    /// [`parse_long_opt`][Self::parse_long_opt] will be called first by
    /// [`Options::next_opt`][crate::Options::next_opt].
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::Argument;
    /// assert_eq!("-abc".parse_short_cluster(), Some("abc"));
    /// assert_eq!("-a".parse_short_cluster(), Some("a"));
    /// assert_eq!("-".parse_short_cluster(), None);
    /// ```
    fn parse_short_cluster(self) -> Option<Self>;

    /// Attempts to consume one short option from a "short option
    /// cluster", as defined by
    /// [`parse_short_cluster`][Self::parse_short_cluster]. Returns the
    /// short option that was consumed and the rest of the cluster (if
    /// non-empty).
    ///
    /// The returned cluster is subject to the same requirements as the
    /// return value of
    /// [`parse_short_cluster`][Self::parse_short_cluster]; namely, its
    /// validity for [`consume_short_opt`][Self::consume_short_opt] or
    /// [`consume_short_val`][Self::consume_short_val].
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::Argument;
    /// assert_eq!("abc".consume_short_opt(), ('a', Some("bc")));
    /// assert_eq!("a".consume_short_opt(), ('a', None));
    /// ```
    fn consume_short_opt(self) -> (Self::ShortOpt, Option<Self>);

    /// Consumes the value of a short option from a "short
    /// option cluster", as defined by
    /// [`parse_short_cluster`][Self::parse_short_cluster]. Returns the
    /// value that was consumed.
    fn consume_short_val(self) -> Self;
}

impl Argument for &'_ str {
    type ShortOpt = char;

    #[inline]
    fn ends_opts(self) -> bool {
        self == "--"
    }

    #[inline]
    fn parse_long_opt(self) -> Option<(Self, Option<Self>)> {
        // Using iterators is slightly faster in release, but many times
        // (>400%) as slow in dev

        let option = self.strip_prefix("--").filter(|s| !s.is_empty())?;

        if let Some((option, value)) = option.split_once('=') {
            Some((option, Some(value)))
        } else {
            Some((option, None))
        }
    }

    #[inline]
    fn parse_short_cluster(self) -> Option<Self> {
        self.strip_prefix('-').filter(|s| !s.is_empty())
    }

    #[inline]
    fn consume_short_opt(self) -> (Self::ShortOpt, Option<Self>) {
        let ch = self
            .chars()
            .next()
            .expect("<&str as getargs::Argument>::consume_short_opt called on an empty string");

        // using `unsafe` here only improves performance by ~10% and is
        // not worth it for losing the "we don't use `unsafe`" guarantee
        (ch, Some(&self[ch.len_utf8()..]).filter(|s| !s.is_empty()))
    }

    #[inline]
    fn consume_short_val(self) -> Self {
        self
    }
}

impl Argument for &'_ [u8] {
    type ShortOpt = u8;

    #[inline]
    fn ends_opts(self) -> bool {
        self == b"--"
    }

    #[inline]
    fn parse_long_opt(self) -> Option<(Self, Option<Self>)> {
        let option = self.strip_prefix(b"--").filter(|a| !a.is_empty())?;

        // This is faster than iterators in dev
        let name = option.split(|b| *b == b'=').next().unwrap();
        let value = if name.len() < option.len() {
            Some(&option[name.len() + 1..])
        } else {
            None
        };

        Some((name, value))
    }

    #[inline]
    fn parse_short_cluster(self) -> Option<Self> {
        self.strip_prefix(b"-").filter(|a| !a.is_empty())
    }

    #[inline]
    fn consume_short_opt(self) -> (Self::ShortOpt, Option<Self>) {
        let (byte, rest) = self
            .split_first()
            .expect("<&[u8] as getargs::Argument>::consume_short_opt called on an empty slice");

        (*byte, Some(rest).filter(|s| !s.is_empty()))
    }

    #[inline]
    fn consume_short_val(self) -> Self {
        self
    }
}
