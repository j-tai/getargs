use test::Bencher;

#[derive(Default)]
pub struct Settings {
    pub short_present1: bool,
    pub short_present2: bool,
    pub short_present3: bool,
    pub long_present1: bool,
    pub long_present2: bool,
    pub long_present3: bool,
    pub short_value1: Option<String>,
    pub short_value2: Option<String>,
    pub short_value3: Option<String>,
    pub long_value1: Option<String>,
    pub long_value2: Option<String>,
    pub long_value3: Option<String>,
}

#[bench]
fn getargs(bencher: &mut Bencher) {
    bencher.iter(|| {
        use crate::ARGS;
        use getargs::{Opt, Options};

        let mut settings = Settings::default();
        let mut opts = Options::new(ARGS.iter().copied());

        while let Some(opt) = opts.next().unwrap() {
            match opt {
                Opt::Short('1') => settings.short_present1 = true,
                Opt::Short('2') => settings.short_present2 = true,
                Opt::Short('3') => settings.short_present3 = true,
                Opt::Long("present1") => settings.long_present1 = true,
                Opt::Long("present2") => settings.long_present2 = true,
                Opt::Long("present3") => settings.long_present3 = true,
                Opt::Short('4') => settings.short_value1 = Some(opts.value().unwrap().to_string()),
                Opt::Short('5') => settings.short_value2 = Some(opts.value().unwrap().to_string()),
                Opt::Short('6') => settings.short_value3 = Some(opts.value().unwrap().to_string()),
                Opt::Long("val1") => settings.long_value1 = Some(opts.value().unwrap().to_string()),
                Opt::Long("val2") => settings.long_value2 = Some(opts.value().unwrap().to_string()),
                Opt::Long("val3") => settings.long_value3 = Some(opts.value().unwrap().to_string()),
                _ => {}
            }
        }

        settings
    })
}

#[bench]
fn getargs4(bencher: &mut Bencher) {
    bencher.iter(|| {
        use crate::ARGS;
        use getargs4::{Opt, Options};

        let mut settings = Settings::default();

        let opts = Options::new(&ARGS);

        while let Some(opt) = opts.next().unwrap() {
            match opt {
                Opt::Short('1') => settings.short_present1 = true,
                Opt::Short('2') => settings.short_present2 = true,
                Opt::Short('3') => settings.short_present3 = true,
                Opt::Long("present1") => settings.long_present1 = true,
                Opt::Long("present2") => settings.long_present2 = true,
                Opt::Long("present3") => settings.long_present3 = true,
                Opt::Short('4') => {
                    settings.short_value1 = Some(opts.value_str().unwrap().to_string())
                }
                Opt::Short('5') => {
                    settings.short_value2 = Some(opts.value_str().unwrap().to_string())
                }
                Opt::Short('6') => {
                    settings.short_value3 = Some(opts.value_str().unwrap().to_string())
                }
                Opt::Long("val1") => {
                    settings.long_value1 = Some(opts.value_str().unwrap().to_string())
                }
                Opt::Long("val2") => {
                    settings.long_value2 = Some(opts.value_str().unwrap().to_string())
                }
                Opt::Long("val3") => {
                    settings.long_value3 = Some(opts.value_str().unwrap().to_string())
                }
                _ => {}
            }
        }

        settings
    })
}

#[bench]
fn clap(bencher: &mut Bencher) {
    bencher.iter(|| {
        use crate::ARGS;
        use clap::{Arg, Command};
        use std::iter::once;

        let mut settings = Settings::default();

        // This isn't at-all representative of a real use case, but
        // shortening the names of these flags literally makes clap get
        // approximately 5% faster in benchmarks.
        let command = Command::new("")
            .arg(Arg::new("a").short('1'))
            .arg(Arg::new("b").short('2'))
            .arg(Arg::new("c").short('3'))
            .arg(Arg::new("d").long("present1"))
            .arg(Arg::new("e").long("present2"))
            .arg(Arg::new("f").long("present3"))
            .arg(Arg::new("g").short('4').takes_value(true))
            .arg(Arg::new("h").short('5').takes_value(true))
            .arg(Arg::new("i").short('6').takes_value(true))
            .arg(Arg::new("j").long("val1").takes_value(true))
            .arg(Arg::new("k").long("val2").takes_value(true))
            .arg(Arg::new("l").long("val3").takes_value(true))
            .get_matches_from(once("a").chain(ARGS.iter().copied()));

        settings.short_present1 = command.is_present("a");
        settings.short_present2 = command.is_present("b");
        settings.short_present3 = command.is_present("c");
        settings.long_present1 = command.is_present("d");
        settings.long_present2 = command.is_present("e");
        settings.long_present3 = command.is_present("f");
        settings.short_value1 = command.value_of("g").map(str::to_string);
        settings.short_value2 = command.value_of("h").map(str::to_string);
        settings.short_value3 = command.value_of("i").map(str::to_string);
        settings.long_value1 = command.value_of("j").map(str::to_string);
        settings.long_value2 = command.value_of("k").map(str::to_string);
        settings.long_value3 = command.value_of("l").map(str::to_string);

        settings
    })
}

#[bench]
fn pico_args(bencher: &mut Bencher) {
    use crate::ARGS;
    use std::ffi::{OsStr, OsString};
    use std::os::unix::ffi::OsStrExt;

    let vec: Vec<OsString> = ARGS
        .iter()
        .copied()
        .map(|s| OsStr::from_bytes(s.as_bytes()).to_os_string())
        .collect();

    bencher.iter(move || {
        use pico_args::Arguments;

        let mut settings = Settings::default();
        let mut arguments = Arguments::from_vec(vec.clone());

        settings.short_present1 = arguments.contains("-1");
        settings.short_present2 = arguments.contains("-2");
        settings.short_present3 = arguments.contains("-3");
        settings.long_present1 = arguments.contains("--present1");
        settings.long_present2 = arguments.contains("--present2");
        settings.long_present3 = arguments.contains("--present3");
        settings.short_value1 = arguments.opt_value_from_str("-4").unwrap();
        settings.short_value2 = arguments.opt_value_from_str("-5").unwrap();
        settings.short_value3 = arguments.opt_value_from_str("-6").unwrap();
        settings.long_value1 = arguments.opt_value_from_str("--val1").unwrap();
        settings.long_value2 = arguments.opt_value_from_str("--val2").unwrap();
        settings.long_value3 = arguments.opt_value_from_str("--val3").unwrap();

        settings
    })
}

#[bench]
fn getopts(bencher: &mut Bencher) {
    bencher.iter(|| {
        use crate::ARGS;
        use getopts::{HasArg, Occur, Options};

        let mut settings = Settings::default();

        let mut opts = Options::new();
        opts.optflag("1", "", "");
        opts.optflag("2", "", "");
        opts.optflag("3", "", "");
        opts.optflag("", "present1", "");
        opts.optflag("", "present2", "");
        opts.optflag("", "present3", "");
        opts.opt("4", "", "", "", HasArg::Yes, Occur::Optional);
        opts.opt("5", "", "", "", HasArg::Yes, Occur::Optional);
        opts.opt("6", "", "", "", HasArg::Yes, Occur::Optional);
        opts.opt("", "val1", "", "", HasArg::Yes, Occur::Optional);
        opts.opt("", "val2", "", "", HasArg::Yes, Occur::Optional);
        opts.opt("", "val3", "", "", HasArg::Yes, Occur::Optional);

        let matches = opts.parse(ARGS).unwrap();

        settings.short_present1 = matches.opt_present("1");
        settings.short_present2 = matches.opt_present("2");
        settings.short_present3 = matches.opt_present("3");
        settings.long_present1 = matches.opt_present("present1");
        settings.long_present2 = matches.opt_present("present2");
        settings.long_present3 = matches.opt_present("present3");
        settings.short_value1 = matches.opt_str("4");
        settings.short_value2 = matches.opt_str("5");
        settings.short_value3 = matches.opt_str("6");
        settings.long_value1 = matches.opt_str("val1");
        settings.long_value2 = matches.opt_str("val2");
        settings.long_value3 = matches.opt_str("val3");

        settings
    })
}

#[bench]
fn getopt(bencher: &mut Bencher) {
    // doesn't support long options lol
    let special = vec![
        String::from("-1"),
        String::from("-3"),
        String::from("-4"),
        String::from("value1"),
        String::from("-6"),
        String::from("value3"),
    ];

    bencher.iter(|| {
        use getopt::{Opt, Parser};

        let mut settings = Settings::default();

        let mut parser = Parser::new(&special, "1234:5:6:");
        parser.set_index(0);

        while let Some(opt) = parser.next().transpose().unwrap() {
            match opt {
                Opt('1', None) => settings.short_present1 = true,
                Opt('2', None) => settings.short_present2 = true,
                Opt('3', None) => settings.short_present3 = true,
                Opt('4', val) => settings.short_value1 = val,
                Opt('5', val) => settings.short_value2 = val,
                Opt('6', val) => settings.short_value3 = val,
                _ => {}
            }
        }

        settings
    })
}

#[bench]
fn lexopt(bencher: &mut Bencher) {
    use crate::ARGS;
    use core::str::FromStr;
    use std::ffi::OsString;

    let args_os = ARGS.map(OsString::from_str).map(Result::unwrap);

    bencher.iter(|| {
        use lexopt::{Arg, Parser};

        let mut settings = Settings::default();

        let mut parser = Parser::from_args(args_os.clone());

        while let Some(opt) = parser.next().unwrap() {
            match opt {
                Arg::Short('1') => settings.short_present1 = true,
                Arg::Short('2') => settings.short_present2 = true,
                Arg::Short('3') => settings.short_present3 = true,
                Arg::Long("present1") => settings.long_present1 = true,
                Arg::Long("present2") => settings.long_present2 = true,
                Arg::Long("present3") => settings.long_present3 = true,
                Arg::Short('4') => {
                    settings.short_value1 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                Arg::Short('5') => {
                    settings.short_value2 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                Arg::Short('6') => {
                    settings.short_value3 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                Arg::Long("val1") => {
                    settings.long_value1 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                Arg::Long("val2") => {
                    settings.long_value2 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                Arg::Long("val3") => {
                    settings.long_value3 =
                        Some(parser.value().unwrap().to_str().unwrap().to_string())
                }
                _ => {}
            }
        }

        settings
    })
}
