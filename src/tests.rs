use super::*;

#[test]
fn no_options() {
    let args = ["foo", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"foo"));
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn short_options() {
    let args = ["-a", "-b", "-3", "-@", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('@'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn short_cluster() {
    let args = ["-ab3@", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('@'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn long_options() {
    let args = ["--ay", "--bee", "--see", "--@3", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("@3"))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn short_option_with_value() {
    let args = ["-a", "ay", "-b", "bee", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value_str(), Ok("ay"));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.value_str(), Ok("bee"));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn short_cluster_with_value() {
    let args = ["-aay", "-3bbee", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value_str(), Ok("ay"));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('3'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.value_str(), Ok("bee"));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn long_option_with_value() {
    let args = ["--ay", "Ay", "--bee=Bee", "--see", "See", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(opts.value_str(), Ok("Ay"));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.value_str(), Ok("Bee"));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
    assert_eq!(opts.value_str(), Ok("See"));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
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
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value_str(), Ok("-ay"));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.value_str(), Ok("--Bee"));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
    assert_eq!(opts.value_str(), Ok("--See"));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('d'))));
    assert_eq!(opts.value_str(), Ok("-dee"));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn no_positional() {
    let args = ["-a", "ay"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value_str(), Ok("ay"));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn long_option_with_empty_value() {
    let args = ["--ay=", "--bee", "", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(opts.value_str(), Ok(""));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.value_str(), Ok(""));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"bar"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn short_option_with_missing_value() {
    let args = ["-a"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value_str(), Err(Error::RequiresValue(Opt::Short('a'))));
}

#[test]
fn long_option_with_unexpected_value() {
    let args = ["--ay=Ay", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(
        opts.next(),
        Some(Err(Error::DoesNotRequireValue(Opt::Long("ay")))),
    );
}

#[test]
fn long_option_with_missing_value() {
    let args = ["--ay"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(opts.value_str(), Err(Error::RequiresValue(Opt::Long("ay"))));
}

#[test]
fn short_option_at_end() {
    let args = ["-a"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn long_option_at_end() {
    let args = ["--ay"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Long("ay"))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn end_of_options() {
    let args = ["-a", "--bee", "--", "--see", "-d"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"--see"));
    assert_eq!(opts.arg_str(), Some(&"-d"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn lone_dash() {
    let args = ["-a", "--bee", "-", "--see", "-d"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"-"));
    assert_eq!(opts.arg_str(), Some(&"--see"));
    assert_eq!(opts.arg_str(), Some(&"-d"));
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn parse_value() {
    let args = ["-a", "3.14", "--bee=5"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.value::<f64>(), Ok(3.14));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("bee"))));
    assert_eq!(opts.value::<i32>(), Ok(5));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), None);
}

#[test]
fn parse_arg() {
    let args = ["-a", "3.14", "5"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg::<f64>(), Some(Ok(3.14)));
    assert_eq!(opts.arg::<i32>(), Some(Ok(5)));
    assert_eq!(opts.arg::<i32>(), None);
}

#[test]
fn parse_invalid_value() {
    let args = ["-a", "3.14.1"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(
        opts.value::<f64>(),
        Err(Error::InvalidValue {
            opt: Opt::Short('a'),
            desc: "invalid float literal".to_string(),
            value: "3.14.1",
        })
    );
}

#[test]
fn parse_invalid_arg() {
    let args = ["-a", "3.14.1"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(
        opts.arg::<f64>(),
        Some(Err(Error::InvalidArg {
            desc: "invalid float literal".to_string(),
            value: "3.14.1",
        }))
    );
}

#[test]
fn subcommand() {
    let args = ["-a", "cmd", "-b", "arg"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"cmd"));
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.arg_str(), Some(&"arg"));
}

// Things you shouldn't need too often

#[test]
fn keep_retrieving_options() {
    let args = ["-a", "ay", "ay2", "bar"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.next(), None);
    assert_eq!(opts.next(), None);
    assert_eq!(opts.next(), None);
}

#[test]
fn keep_retrieving_options_2() {
    let args = ["-a", "--", "-b", "--see"];
    let opts = Options::new(&args);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('a'))));
    assert_eq!(opts.next(), None);
    assert_eq!(opts.next(), Some(Ok(Opt::Short('b'))));
    assert_eq!(opts.next(), Some(Ok(Opt::Long("see"))));
    assert_eq!(opts.next(), None);
}

// Things you definitely shouldn't do

#[test]
#[should_panic]
fn keep_taking_values() {
    let args = ["-a", "ay", "ay2", "bar"];
    let opts = Options::new(&args);
    let _ = opts.next(); // -a
    let _ = opts.value_str(); // ay
    let _ = opts.value_str(); // panic: cannot get 2 values
}

#[test]
fn keep_taking_args() {
    let args = ["-a", "ay"];
    let opts = Options::new(&args);
    assert_eq!(opts.arg_str(), Some(&"-a"));
    assert_eq!(opts.arg_str(), Some(&"ay"));
    assert_eq!(opts.arg_str(), None);
    assert_eq!(opts.arg_str(), None);
    assert_eq!(opts.arg_str(), None);
    assert_eq!(opts.arg_str(), None);
}

#[test]
#[should_panic]
fn value_without_option() {
    let args = ["-a", "ay"];
    let opts = Options::new(&args);
    let _ = opts.value_str(); // no option retrieved yet
}

#[test]
#[should_panic]
fn value_after_arg() {
    let args = ["ay", "bee"];
    let opts = Options::new(&args);
    let _ = opts.arg_str(); // ay
    let _ = opts.value_str(); // no option retrieved yet
}
