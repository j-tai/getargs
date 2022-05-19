use super::*;

#[test]
fn no_options() {
    let args = ["foo", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("foo"));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn short_options() {
    let args = ["-a", "-b", "-3", "-@", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('@'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn short_cluster() {
    let args = ["-ab3@", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('@'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn long_options() {
    let args = ["--ay", "--bee", "--see", "--@3", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("@3"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn short_option_with_value() {
    let args = ["-a", "ay", "-b", "bee", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.value(), Ok("bee"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn short_cluster_with_value() {
    let args = ["-aay", "-3bbee", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('3'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.value(), Ok("bee"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn long_option_with_value() {
    let args = ["--ay", "Ay", "--bee=Bee", "--see", "See", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Ok("Ay"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok("Bee"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.value(), Ok("See"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
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
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("-ay"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok("--Bee"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.value(), Ok("--See"));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('d'))));
    assert_eq!(opts.value(), Ok("-dee"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn no_positional() {
    let args = ["-a", "ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Ok("ay"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), None);
}

#[test]
fn long_option_with_empty_value() {
    let args = ["--ay=", "--bee", "", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Ok(""));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.value(), Ok(""));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("bar"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn short_option_with_missing_value() {
    let args = ["-a"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Short('a'))));
}

#[test]
fn long_option_with_unexpected_value() {
    let args = ["--ay=Ay", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(
        opts.next(),
        Err(Error::DoesNotRequireValue(Opt::Long("ay"))),
    );
}

#[test]
fn long_option_with_missing_value() {
    let args = ["--ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.value(), Err(Error::RequiresValue(Opt::Long("ay"))));
}

#[test]
fn short_option_at_end() {
    let args = ["-a"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), None);
}

#[test]
fn long_option_at_end() {
    let args = ["--ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Long("ay"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), None);
}

#[test]
fn end_of_options() {
    let args = ["-a", "--bee", "--", "--see", "-d"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.arg(), Some("--see"));
    assert_eq!(opts.arg(), Some("-d"));
    assert_eq!(opts.arg(), None);
    assert!(!opts.opts_ended());
}

#[test]
fn lone_dash() {
    let args = ["-a", "--bee", "-", "--see", "-d"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("bee"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("-"));
    assert_eq!(opts.arg(), Some("--see"));
    assert_eq!(opts.arg(), Some("-d"));
    assert_eq!(opts.arg(), None);
}

#[test]
fn subcommand() {
    let args = ["-a", "cmd", "-b", "arg"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("cmd"));
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("arg"));
}

// Things you shouldn't need too often

#[test]
fn keep_retrieving_options() {
    let args = ["-a", "ay", "ay2", "bar"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.next(), Ok(None));
}

#[test]
fn keep_retrieving_options_2() {
    let args = ["-a", "--", "-b", "--see"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('a'))));
    assert_eq!(opts.next(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.next(), Ok(Some(Opt::Short('b'))));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("see"))));
    assert_eq!(opts.next(), Ok(None));
    assert!(!opts.opts_ended());
}

// Things you definitely shouldn't do

#[test]
#[should_panic]
fn keep_taking_values() {
    let args = ["-a", "ay", "ay2", "bar"];
    let mut opts = Options::new(args.into_iter());
    let _ = opts.next(); // -a
    let _ = opts.value(); // ay
    let _ = opts.value(); // panic: cannot get 2 values
}

#[test]
fn keep_taking_args() {
    let args = ["-a", "ay"];
    let mut opts = Options::new(args.into_iter());
    assert_eq!(opts.arg(), Some("-a"));
    assert_eq!(opts.arg(), Some("ay"));
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
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
    let _ = opts.arg(); // ay
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

    assert_eq!(opts.next(), Ok(Some(Opt::Short(b'o'))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next(), Ok(Some(Opt::Long(b"opt".as_slice()))));
    assert_eq!(opts.value(), Ok(b"HI".as_slice()));
    assert_eq!(opts.next(), Ok(Some(Opt::Short(b'o'))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next(), Ok(Some(Opt::Long(b"opt".as_slice()))));
    assert_eq!(opts.value(), Ok(b"hi".as_slice()));
    assert_eq!(opts.next(), Ok(Some(Opt::Long(b"optional".as_slice()))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next(), Ok(Some(Opt::Long(b"optional".as_slice()))));
    assert_eq!(opts.value_opt(), Some(b"value".as_slice()));
    assert_eq!(opts.next(), Ok(Some(Opt::Short(b'O'))));
    assert_eq!(opts.value_opt(), None);
    assert_eq!(opts.next(), Ok(Some(Opt::Short(b'O'))));
    assert_eq!(opts.value_opt(), Some(b"value".as_slice()));
    assert_eq!(opts.next(), Ok(None));
    assert!(opts.opts_ended());
    assert_eq!(opts.arg(), Some(b"one".as_slice()));
    assert_eq!(opts.arg(), Some(b"two".as_slice()));
    assert_eq!(opts.arg(), None);
    assert!(!opts.opts_ended());
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

    assert_eq!(opts.next(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("positional"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("positional2"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("positional3"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("flag3"))));
    assert_eq!(opts.value(), Ok("value"));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), Some("final"));
    assert_eq!(opts.next(), Ok(Some(Opt::Long("justkidding"))));
    assert_eq!(opts.next(), Ok(None));
    assert_eq!(opts.arg(), None);
}

#[test]
fn does_not_require_value_continue() {
    let args = ["--flag=value", "--flag2"];
    let mut opts = Options::new(args.into_iter());

    assert_eq!(opts.next(), Ok(Some(Opt::Long("flag"))));
    assert_eq!(
        opts.next(),
        Err(Error::DoesNotRequireValue(Opt::Long("flag")))
    );
    assert_eq!(opts.next(), Ok(Some(Opt::Long("flag2"))));
    assert_eq!(opts.next(), Ok(None));
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
    assert_eq!(opts.arg(), Some("fsa"));
    assert_eq!(opts.arg(), Some("N"));
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    opts.restart();
    assert_eq!(opts.arg(), Some("fsa"));
    assert_eq!(opts.arg(), Some("N"));
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
    assert_eq!(opts.arg(), None);
}
