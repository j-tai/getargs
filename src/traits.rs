use core::fmt::{Debug, Display, Formatter, Write};
#[cfg(feature = "std")]
use std::ffi::OsStr;

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
    /// assert_eq!("--flag".parse_long_opt(), Ok(Some(("flag", None))));
    /// assert_eq!("--flag=value".parse_long_opt(), Ok(Some(("flag", Some("value")))));
    /// assert_eq!("--flag=".parse_long_opt(), Ok(Some(("flag", Some("")))));
    /// assert_eq!("-a".parse_long_opt(), Ok(None));
    ///// assert_eq!(b"--\xFF".parse_long_opt(), Err(ConversionError));
    /// ```
    fn parse_long_opt<'opt>(self) -> Result<Self, Option<(&'opt str, Option<Self>)>>
    where
        Self: 'opt;

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
    /// assert_eq!("-abc".parse_short_cluster(true), Some("abc"));
    /// assert_eq!("-a".parse_short_cluster(true), Some("a"));
    /// assert_eq!("-".parse_short_cluster(true), None);
    /// assert_eq!("-1".parse_short_cluster(true), Some("1"));
    /// assert_eq!("-1".parse_short_cluster(false), None);
    /// assert_eq!("-a".parse_short_cluster(false), Some("a"));
    /// ```
    fn parse_short_cluster(self, allow_number: bool) -> Option<Self>;

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
    /// assert_eq!("abc".consume_short_opt(), Ok(('a', Some("bc"))));
    /// assert_eq!("a".consume_short_opt(), Ok(('a', None)));
    /// ```
    fn consume_short_opt(self) -> Result<Self, (char, Option<Self>)>;

    /// Consumes the value of a short option from a "short
    /// option cluster", as defined by
    /// [`parse_short_cluster`][Self::parse_short_cluster]. Returns the
    /// value that was consumed.
    fn consume_short_val(self) -> Self;

    /// Returns an object implementing Display which can be used to format the
    /// Argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use getargs::Argument;
    /// assert_eq!(b"abc".display().to_string(), "abc");
    fn display(self) -> impl Display;
}

#[inline]
fn is_number(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    #[derive(PartialEq)]
    enum State {
        Integer,
        Separator,
        Fractional,
    }
    let mut state = State::Integer;
    for b in bytes {
        state = match state {
            State::Integer => match b {
                b'.' => State::Separator,
                b'0'..=b'9' => State::Integer,
                _ => return false,
            },
            State::Separator | State::Fractional => match b {
                b'0'..=b'9' => State::Fractional,
                _ => return false,
            },
        }
    }
    state != State::Separator
}

#[derive(Debug, PartialEq, Clone, Eq, Copy)]
pub struct ConversionError<A: Argument> {
    option: A,
}

impl<A: Argument> ConversionError<A> {
    fn new(option: A) -> Self {
        Self { option }
    }
}

impl<A: Argument> Display for ConversionError<A> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "invalid UTF-8 within option: {}", self.option.display())
    }
}

#[cfg(feature = "std")]
impl<A: Argument> std::error::Error for ConversionError<A> {}

pub type Result<A, T> = core::result::Result<T, ConversionError<A>>;

impl Argument for &str {
    #[inline]
    fn ends_opts(self) -> bool {
        self == "--"
    }

    #[inline]
    fn parse_long_opt<'opt>(self) -> Result<Self, Option<(&'opt str, Option<Self>)>>
    where
        Self: 'opt,
    {
        // Using iterators is slightly faster in release, but many times
        // (>400%) as slow in dev

        let Some(option) = self.strip_prefix("--").filter(|s| !s.is_empty()) else {
            return Ok(None);
        };

        if let Some((option, value)) = option.split_once('=') {
            Ok(Some((option, Some(value))))
        } else {
            Ok(Some((option, None)))
        }
    }

    #[inline]
    fn parse_short_cluster(self, allow_number: bool) -> Option<Self> {
        self.strip_prefix('-')
            .filter(|s| !s.is_empty() && (allow_number || !is_number(s.as_ref())))
    }

    #[inline]
    fn consume_short_opt(self) -> Result<Self, (char, Option<Self>)> {
        let ch = self
            .chars()
            .next()
            .expect("<&str as getargs::Argument>::consume_short_opt called on an empty string");

        // using `unsafe` here only improves performance by ~10% and is
        // not worth it for losing the "we don't use `unsafe`" guarantee
        Ok((ch, Some(&self[ch.len_utf8()..]).filter(|s| !s.is_empty())))
    }

    #[inline]
    fn consume_short_val(self) -> Self {
        self
    }

    #[inline]
    fn display(self) -> impl Display {
        self
    }
}

struct DisplaySliceU8<'a> {
    slice: &'a [u8],
}

impl Display for DisplaySliceU8<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str("")?;
        for chunk in self.slice.utf8_chunks() {
            f.write_str(chunk.valid())?;
            let invalid = chunk.invalid();
            if !invalid.is_empty() {
                f.write_char(char::REPLACEMENT_CHARACTER)?;
            }
        }
        Ok(())
    }
}

impl Argument for &[u8] {
    #[inline]
    fn ends_opts(self) -> bool {
        self == b"--"
    }

    #[inline]
    fn parse_long_opt<'opt>(self) -> Result<Self, Option<(&'opt str, Option<Self>)>>
    where
        Self: 'opt,
    {
        let Some(option) = self.strip_prefix(b"--").filter(|a| !a.is_empty()) else {
            return Ok(None);
        };

        // This is faster than iterators in dev
        let name = option.split(|b| *b == b'=').next().unwrap();
        let value = if name.len() < option.len() {
            Some(&option[name.len() + 1..])
        } else {
            None
        };

        let Ok(name) = core::str::from_utf8(name) else {
            return Err(ConversionError::new(self));
        };

        Ok(Some((name, value)))
    }

    #[inline]
    fn parse_short_cluster(self, allow_number: bool) -> Option<Self> {
        self.strip_prefix(b"-")
            .filter(|a| !a.is_empty() && (allow_number || !is_number(a)))
    }

    #[inline]
    fn consume_short_opt(self) -> Result<Self, (char, Option<Self>)> {
        if self[0].is_ascii() {
            Ok((self[0] as char, Some(&self[1..]).filter(|s| !s.is_empty())))
        } else {
            let Some(ch) = self
                .utf8_chunks()
                .next()
                .expect("<&[u8] as getargs::Argument>::consume_short_opt called on an empty string")
                .valid()
                .chars()
                .next()
            else {
                return Err(ConversionError::new(self));
            };

            let rest = &self[ch.len_utf8()..];
            Ok((ch, Some(rest).filter(|s| !s.is_empty())))
        }
    }

    #[inline]
    fn consume_short_val(self) -> Self {
        self
    }

    #[inline]
    fn display(self) -> impl Display {
        DisplaySliceU8 { slice: self }
    }
}

#[cfg(feature = "std")]
impl Argument for &OsStr {
    #[inline]
    fn ends_opts(self) -> bool {
        self.as_encoded_bytes().ends_opts()
    }

    #[inline]
    fn parse_long_opt<'opt>(self) -> Result<Self, Option<(&'opt str, Option<Self>)>>
    where
        Self: 'opt,
    {
        self.as_encoded_bytes()
            .parse_long_opt()
            .map(|o| {
                o.map(|t| {
                    (
                        t.0,
                        t.1.map(|s| unsafe { OsStr::from_encoded_bytes_unchecked(s) }),
                    )
                })
            })
            .map_err(|e| {
                ConversionError::new(unsafe { OsStr::from_encoded_bytes_unchecked(e.option) })
            })
    }

    #[inline]
    fn parse_short_cluster(self, allow_number: bool) -> Option<Self> {
        self.as_encoded_bytes()
            .parse_short_cluster(allow_number)
            .map(|s| unsafe { OsStr::from_encoded_bytes_unchecked(s) })
    }

    #[inline]
    fn consume_short_opt(self) -> Result<Self, (char, Option<Self>)> {
        self.as_encoded_bytes()
            .consume_short_opt()
            .map(|t| {
                (
                    t.0,
                    t.1.map(|s| unsafe { OsStr::from_encoded_bytes_unchecked(s) }),
                )
            })
            .map_err(|e| {
                ConversionError::new(unsafe { OsStr::from_encoded_bytes_unchecked(e.option) })
            })
    }

    #[inline]
    fn consume_short_val(self) -> Self {
        self
    }

    fn display(self) -> impl Display {
        DisplaySliceU8 {
            slice: self.as_encoded_bytes(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::is_number;
    #[test]
    fn test_is_number() {
        assert!(is_number(b"123"));
        assert!(is_number(b"123.456"));
        assert!(is_number(b".123"));
        assert!(is_number(b"1"));
        assert!(is_number(b".1"));
        assert!(is_number(b"0"));
        assert!(is_number(b"1"));
        assert!(is_number(b"2"));
        assert!(is_number(b"3"));
        assert!(is_number(b"4"));
        assert!(is_number(b"5"));
        assert!(is_number(b"6"));
        assert!(is_number(b"7"));
        assert!(is_number(b"8"));
        assert!(is_number(b"9"));
        assert!(is_number(b"0123456789"));
    }

    #[test]
    fn test_not_is_number() {
        assert!(!is_number(b""));
        assert!(!is_number(b"a"));
        assert!(!is_number(b"0a"));
        assert!(!is_number(b"a0"));
        assert!(!is_number(b"1..2"));
        assert!(!is_number(b"1."));
        assert!(!is_number(b"123."));
        assert!(!is_number(b"123..456"));
        assert!(!is_number(b"1234b"));
        assert!(!is_number(b"asdf1234foo"));
    }
}
