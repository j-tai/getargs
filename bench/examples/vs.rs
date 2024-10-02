use bench::{ARGS, ARGS_BYTES};
use getargs::Argument;
use std::ffi::OsStr;
use std::hint::black_box;
use std::time::Instant;

#[derive(Default)]
pub struct Settings<A: Argument> {
    pub short_present1: bool,
    pub short_present2: bool,
    pub short_present3: bool,
    pub long_present1: bool,
    pub long_present2: bool,
    pub long_present3: bool,
    pub short_value1: Option<A>,
    pub short_value2: Option<A>,
    pub short_value3: Option<A>,
    pub long_value1: Option<A>,
    pub long_value2: Option<A>,
    pub long_value3: Option<A>,
}

// Broken lifetimes in 0.4.1: `'str` is needed on the slice...
#[inline(never)]
fn getargs4<'str>(args: &'str [&'str str]) -> Settings<&'str str> {
    use getargs4::{Opt, Options};

    let mut settings = Settings::default();
    let opts = Options::new(args);

    while let Some(opt) = opts.next().unwrap() {
        match opt {
            Opt::Short('1') => settings.short_present1 = true,
            Opt::Short('2') => settings.short_present2 = true,
            Opt::Short('3') => settings.short_present3 = true,
            Opt::Long("present1") => settings.long_present1 = true,
            Opt::Long("present2") => settings.long_present2 = true,
            Opt::Long("present3") => settings.long_present3 = true,
            Opt::Short('4') => settings.short_value1 = Some(opts.value_str().unwrap()),
            Opt::Short('5') => settings.short_value2 = Some(opts.value_str().unwrap()),
            Opt::Short('6') => settings.short_value3 = Some(opts.value_str().unwrap()),
            Opt::Long("val1") => settings.long_value1 = Some(opts.value_str().unwrap()),
            Opt::Long("val2") => settings.long_value2 = Some(opts.value_str().unwrap()),
            Opt::Long("val3") => settings.long_value3 = Some(opts.value_str().unwrap()),
            _ => {}
        }
    }

    settings
}

#[inline(never)]
fn getargs5<'str, I: Iterator<Item = &'str str>>(iter: I) -> Settings<&'str str> {
    use getargs::{Opt, Options};

    let mut settings = Settings::default();
    let mut opts = Options::new(iter);

    while let Some(opt) = opts.next_opt().unwrap() {
        match opt {
            Opt::Short('1') => settings.short_present1 = true,
            Opt::Short('2') => settings.short_present2 = true,
            Opt::Short('3') => settings.short_present3 = true,
            Opt::Long("present1") => settings.long_present1 = true,
            Opt::Long("present2") => settings.long_present2 = true,
            Opt::Long("present3") => settings.long_present3 = true,
            Opt::Short('4') => settings.short_value1 = Some(opts.value().unwrap()),
            Opt::Short('5') => settings.short_value2 = Some(opts.value().unwrap()),
            Opt::Short('6') => settings.short_value3 = Some(opts.value().unwrap()),
            Opt::Long("val1") => settings.long_value1 = Some(opts.value().unwrap()),
            Opt::Long("val2") => settings.long_value2 = Some(opts.value().unwrap()),
            Opt::Long("val3") => settings.long_value3 = Some(opts.value().unwrap()),
            _ => {}
        }
    }

    settings
}

#[inline(never)]
fn getargs5b<'arg, I: Iterator<Item = &'arg [u8]>>(iter: I) -> Settings<&'arg [u8]> {
    use getargs::{Opt, Options};

    let mut settings = Settings::default();
    let mut opts = Options::new(iter);

    while let Some(opt) = opts.next_opt().unwrap() {
        match opt {
            Opt::Short('1') => settings.short_present1 = true,
            Opt::Short('2') => settings.short_present2 = true,
            Opt::Short('3') => settings.short_present3 = true,
            Opt::Long("present1") => settings.long_present1 = true,
            Opt::Long("present2") => settings.long_present2 = true,
            Opt::Long("present3") => settings.long_present3 = true,
            Opt::Short('4') => settings.short_value1 = Some(opts.value().unwrap()),
            Opt::Short('5') => settings.short_value2 = Some(opts.value().unwrap()),
            Opt::Short('6') => settings.short_value3 = Some(opts.value().unwrap()),
            Opt::Long("val1") => settings.long_value1 = Some(opts.value().unwrap()),
            Opt::Long("val2") => settings.long_value2 = Some(opts.value().unwrap()),
            Opt::Long("val3") => settings.long_value3 = Some(opts.value().unwrap()),
            _ => {}
        }
    }

    settings
}

#[inline(never)]
fn getargs5o<'arg, I: Iterator<Item = &'arg OsStr>>(iter: I) -> Settings<&'arg OsStr> {
    use getargs::{Opt, Options};

    let mut settings = Settings::default();
    let mut opts = Options::new(iter);

    while let Some(opt) = opts.next_opt().unwrap() {
        match opt {
            Opt::Short('1') => settings.short_present1 = true,
            Opt::Short('2') => settings.short_present2 = true,
            Opt::Short('3') => settings.short_present3 = true,
            Opt::Long("present1") => settings.long_present1 = true,
            Opt::Long("present2") => settings.long_present2 = true,
            Opt::Long("present3") => settings.long_present3 = true,
            Opt::Short('4') => settings.short_value1 = Some(opts.value().unwrap()),
            Opt::Short('5') => settings.short_value2 = Some(opts.value().unwrap()),
            Opt::Short('6') => settings.short_value3 = Some(opts.value().unwrap()),
            Opt::Long("val1") => settings.long_value1 = Some(opts.value().unwrap()),
            Opt::Long("val2") => settings.long_value2 = Some(opts.value().unwrap()),
            Opt::Long("val3") => settings.long_value3 = Some(opts.value().unwrap()),
            _ => {}
        }
    }

    settings
}

fn main() {
    const ITERATIONS: usize = 10_000_000;

    let a = Instant::now();

    for _ in 0..ITERATIONS {
        black_box(getargs4(&ARGS));
    }

    let b = Instant::now();

    for _ in 0..ITERATIONS {
        black_box(getargs5(ARGS.iter().copied()));
    }

    let c = Instant::now();

    for _ in 0..ITERATIONS {
        black_box(getargs5b(ARGS_BYTES.iter().copied()));
    }

    let d = Instant::now();

    for _ in 0..ITERATIONS {
        black_box(getargs5o(ARGS.iter().copied().map(AsRef::as_ref)));
    }

    let e = Instant::now();

    eprintln!("getargs4:  {}ns", (b - a).as_nanos() / ITERATIONS as u128);
    eprintln!("getargs5:  {}ns", (c - b).as_nanos() / ITERATIONS as u128);
    eprintln!("getargs5b: {}ns", (d - c).as_nanos() / ITERATIONS as u128);
    eprintln!("getargs5o: {}ns", (e - d).as_nanos() / ITERATIONS as u128);
}
