use std::ffi::OsStr;

use super::*;

#[test]
fn no_options() {
    let args = ["foo", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("foo"));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn short_options() {
    let args = ["-a", "-b", "-3", "-@", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('@'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn short_cluster() {
    let args = ["-ab3@", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('@'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn long_options() {
    let args = ["--ay", "--bee", "--see", "--@3", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("@3"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn short_option_with_value() {
    let args = ["-a", "ay", "-b", "bee", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.value(), Ok("bee"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn short_cluster_with_value() {
    let args = ["-aay", "-3bbee", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.value(), Ok("bee"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn long_option_with_value() {
    let args = ["--ay", "Ay", "--bee=Bee", "--see", "See", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Ok("Ay"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok("Bee"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.value(), Ok("See"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn value_with_dash() {
    let args = [
        "-a",
        "-ay",
        "--bee=--Bee",
        "--see",
        "--See",
        "-d-dee",
        "bar",
    ];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("-ay"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok("--Bee"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.value(), Ok("--See"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('d'))));
    assert_eq!(opts.value(), Ok("-dee"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn no_positional() {
    let args = ["-a", "ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn long_option_with_empty_value() {
    let args = ["--ay=", "--bee", "", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Ok(""));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok(""));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("bar"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn short_option_with_missing_value() {
    let args = ["-a"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Short('a'))));
    assert!(opts.is_empty());
}

#[test]
fn long_option_with_unexpected_value() {
    let args = ["--ay=Ay", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(
        opts.next_opt(),
        Err(Error::DoesNotRequireValue(Opt::Long("ay"))),
    );
    assert!(!opts.is_empty());
}

#[test]
fn long_option_with_missing_value() {
    let args = ["--ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Long("ay"))));
    assert!(opts.is_empty());
}

#[test]
fn short_option_at_end() {
    let args = ["-a"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn long_option_at_end() {
    let args = ["--ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn end_of_options() {
    let args = ["-a", "--bee", "--", "--see", "-d"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.next_positional(), Some("--see"));
    assert_eq!(opts.next_positional(), Some("-d"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.opts_ended());
    assert!(opts.is_empty());
}

#[test]
fn lone_dash() {
    let args = ["-a", "--bee", "-", "--see", "-d"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("-"));
    assert_eq!(opts.next_positional(), Some("--see"));
    assert_eq!(opts.next_positional(), Some("-d"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn subcommand() {
    let args = ["-a", "cmd", "-b", "arg"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("cmd"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("arg"));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn options_anywhere() {
    let args = ["-a", "1", "--foo", "2", "3", "-bc", "4"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('a'))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("1"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Long("foo"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("2"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("3"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('b'))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('c'))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("4"))));
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn options_anywhere_with_values() {
    let args = ["-a", "1", "--foo", "2", "3", "-bc", "4"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('a'))));
    assert_eq!(opts.value(), Ok("1"));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Long("foo"))));
    assert_eq!(opts.value(), Ok("2"));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("3"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('b'))));
    assert_eq!(opts.value(), Ok("c"));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("4"))));
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn options_anywhere_with_end() {
    let args = ["-a", "1", "--foo", "2", "--", "-bc", "--positional"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('a'))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("1"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Long("foo"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("2"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("-bc"))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("--positional"))));
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn next_opt_empty() {
    let mut opts = Options::new(core::iter::empty::<&str>());
    assert!(!opts.is_empty());
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn next_arg_empty() {
    let mut opts = Options::new(core::iter::empty::<&str>());
    assert!(!opts.is_empty());
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn next_positional_empty() {
    let mut opts = Options::new(core::iter::empty::<&str>());
    assert!(!opts.is_empty());
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn keep_retrieving_options() {
    let args = ["-a", "ay", "ay2", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(!opts.is_empty());
}

#[test]
fn keep_retrieving_options_2() {
    let args = ["-a", "--", "-b", "--see"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(!opts.opts_ended());
    assert!(opts.is_empty());
}

#[test]
fn keep_retrieving_args() {
    let args = ["-a", "foo"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Short('a'))));
    assert_eq!(opts.next_arg(), Ok(Some(Arg::Positional("foo"))));
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
    assert_eq!(opts.next_arg(), Ok(None));
    assert_eq!(opts.next_arg(), Ok(None));
    assert_eq!(opts.next_arg(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn keep_retrieving_positional() {
    let args = ["-a", "ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next_positional(), Some("-a"));
    assert_eq!(opts.next_positional(), Some("ay"));
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
#[should_panic]
fn keep_taking_values() {
    let args = ["-a", "ay", "ay2", "bar"];
    let mut opts = Options::new(args.into_iter());
    let _ = opts.next_opt(); // -a
    let _ = opts.value(); // ay
    let _ = opts.value(); // panic: cannot get 2 values
}

#[test]
#[should_panic]
fn value_without_option() {
    let args = ["-a", "ay"];
    let mut opts = Options::new(args.into_iter());
    let _ = opts.value(); // no option retrieved yet
}

#[test]
#[should_panic]
fn value_after_arg() {
    let args = ["ay", "bee"];
    let mut opts = Options::new(args.into_iter());
    let _ = opts.next_positional(); // ay
    let _ = opts.value(); // no option retrieved yet
}

#[test]
fn bytes() {
    let args = [
        b"-ohi".as_slice(),
        b"--opt=HI",
        b"-o",
        b"hi",
        b"--opt",
        b"hi",
        b"--optional",
        b"--optional=value",
        b"-O",
        b"-Ovalue",
        b"--",
        b"one",
        b"two",
    ];

    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    assert_eq!(opts.value(), Ok(b"HI".as_slice()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("optional"))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("optional"))));
    assert_eq!(opts.value_opt(), Some(b"value".as_slice()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('O'))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('O'))));
    assert_eq!(opts.value_opt(), Some(b"value".as_slice()));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.next_positional(), Some(b"one".as_slice()));
    assert_eq!(opts.next_positional(), Some(b"two".as_slice()));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.opts_ended());
    assert!(opts.is_empty());
}

#[test]
fn alternating() {
    let args = [
        "--flag",
        "positional",
        "--flag2",
        "positional2",
        "positional3",
        "--flag3=value",
        "final",
        "--justkidding",
    ];

    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("positional"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("positional2"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("positional3"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag3"))));
    assert_eq!(opts.value(), Ok("value"));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), Some("final"));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("justkidding"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn does_not_require_value_continue() {
    let args = ["--flag=value", "--flag2"];
    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(
        opts.next_opt(),
        Err(Error::DoesNotRequireValue(Opt::Long("flag"))),
    );
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.is_empty());
}

#[test]
fn args() {
    let args = ["--flag=value", "--flag2", "--", "arg1", "arg2"];
    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(
        opts.next_opt(),
        Err(Error::DoesNotRequireValue(Opt::Long("flag")))
    );
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert!(!opts.is_empty());

    let mut args = opts.positionals();

    assert_eq!(args.next(), Some("arg1"));
    assert_eq!(args.next(), Some("arg2"));
    assert_eq!(args.next(), None);
    assert!(opts.is_empty());
}

#[test]
fn into_args() {
    let args = ["--flag=value", "--flag2", "--", "arg1", "arg2"];
    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(
        opts.next_opt(),
        Err(Error::DoesNotRequireValue(Opt::Long("flag")))
    );
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert!(!opts.is_empty());

    let mut args = opts.into_positionals();

    assert_eq!(args.next(), Some("arg1"));
    assert_eq!(args.next(), Some("arg2"));
    assert_eq!(args.next(), None);
}

struct RepeatingIterator<T, I: Iterator<Item = T>, F: FnMut() -> I>(Option<I>, F);

impl<T, I: Iterator<Item = T>, F: FnMut() -> I> Iterator for RepeatingIterator<T, I, F> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.get_or_insert_with(&mut self.1).next() {
            some @ Some(_) => some,
            None => {
                self.0.take();
                None
            }
        }
    }
}

impl<T, I: Iterator<Item = T>, F: FnMut() -> I> RepeatingIterator<T, I, F> {
    pub fn new(factory: F) -> Self {
        Self(None, factory)
    }
}

#[test]
fn repeating_iterator() {
    let args = ["fsa", "N"];
    let iter = RepeatingIterator::new(|| args.iter().copied());
    let mut opts = Options::new(iter);
    assert_eq!(opts.next_positional(), Some("fsa"));
    assert_eq!(opts.next_positional(), Some("N"));
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
    opts.restart();
    assert!(!opts.is_empty());
    assert_eq!(opts.next_positional(), Some("fsa"));
    assert_eq!(opts.next_positional(), Some("N"));
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert_eq!(opts.next_positional(), None);
    assert!(opts.is_empty());
}

#[test]
fn os_str() {
    let args = [
        "-ohi",
        "--opt=HI",
        "-o",
        "hi",
        "--opt",
        "hi",
        "--optional",
        "--optional=value",
        "-O",
        "-Ovalue",
        "--",
        "one",
        "two",
    ];

    let mut opts = Options::<'_, &OsStr, _>::new(args.into_iter().map(AsRef::as_ref));

    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    assert_eq!(opts.value(), Ok("hi".as_ref()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    assert_eq!(opts.value(), Ok("HI".as_ref()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('o'))));
    assert_eq!(opts.value(), Ok("hi".as_ref()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("opt"))));
    assert_eq!(opts.value(), Ok("hi".as_ref()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("optional"))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Long("optional"))));
    assert_eq!(opts.value_opt(), Some("value".as_ref()));
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('O'))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next_opt(), Ok(Some(Opt::Short('O'))));
    assert_eq!(opts.value_opt(), Some("value".as_ref()));
    assert_eq!(opts.next_opt(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.next_positional(), Some("one".as_ref()));
    assert_eq!(opts.next_positional(), Some("two".as_ref()));
    assert_eq!(opts.next_positional(), None);
    assert!(opts.opts_ended());
    assert!(opts.is_empty());
}
