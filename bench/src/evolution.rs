#![allow(non_snake_case)]

use std::ffi::OsStr;

use crate::{ARGS, ARGS_BYTES};
use getargs::Argument;
use test::Bencher;

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
#[inline(always)]
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

#[inline(always)]
fn getargs5<'str, I: Iterator<Item = &'str str>>(iter: I) -> Settings<&'str str> {
    use getargs5::{Opt, Options};

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

#[inline(always)]
fn getargs5b<'arg, I: Iterator<Item = &'arg [u8]>>(iter: I) -> Settings<&'arg [u8]> {
    use getargs5::{Opt, Options};

    let mut settings = Settings::default();
    let mut opts = Options::new(iter);

    while let Some(opt) = opts.next_opt().unwrap() {
        match opt {
            Opt::Short(b'1') => settings.short_present1 = true,
            Opt::Short(b'2') => settings.short_present2 = true,
            Opt::Short(b'3') => settings.short_present3 = true,
            Opt::Long(b"present1") => settings.long_present1 = true,
            Opt::Long(b"present2") => settings.long_present2 = true,
            Opt::Long(b"present3") => settings.long_present3 = true,
            Opt::Short(b'4') => settings.short_value1 = Some(opts.value().unwrap()),
            Opt::Short(b'5') => settings.short_value2 = Some(opts.value().unwrap()),
            Opt::Short(b'6') => settings.short_value3 = Some(opts.value().unwrap()),
            Opt::Long(b"val1") => settings.long_value1 = Some(opts.value().unwrap()),
            Opt::Long(b"val2") => settings.long_value2 = Some(opts.value().unwrap()),
            Opt::Long(b"val3") => settings.long_value3 = Some(opts.value().unwrap()),
            _ => {}
        }
    }

    settings
}

#[inline(always)]
fn getargsL<'str, I: Iterator<Item = &'str str>>(iter: I) -> Settings<&'str str> {
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

#[inline(always)]
fn getargsLb<'arg, I: Iterator<Item = &'arg [u8]>>(iter: I) -> Settings<&'arg [u8]> {
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

#[inline(always)]
fn getargsLo<'arg, I: Iterator<Item = &'arg OsStr>>(iter: I) -> Settings<&'arg OsStr> {
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

#[bench]
#[inline(never)]
fn getargs4_varied_small(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS));
}

#[bench]
#[inline(never)]
fn getargs5_varied_small(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_varied_small(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_varied_small(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_varied_small(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_varied_small(bencher: &mut Bencher) {
    let args_os: Box<[&OsStr]> = ARGS.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_LONG: [&str; 1000] = ["--dsfigadsjfdgsfjkasbfjksdfabsdbfdaf"; 1000];
pub const ARGS_LONG_BYTES: [&[u8]; 1000] = [b"--dsfigadsjfdgsfjkasbfjksdfabsdbfdaf"; 1000];

#[bench]
#[inline(never)]
fn getargs4_long(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_LONG));
}

#[bench]
#[inline(never)]
fn getargs5_long(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_LONG.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_long(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_LONG_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_long(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_LONG.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_long(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_LONG_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_long(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_LONG.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_SHORT_CLUSTER: [&str; 1000] =
    ["-rjryets8kzrlxu7lzvnmsooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

pub const ARGS_SHORT_CLUSTER_BYTES: [&[u8]; 1000] =
    [b"-rjryets8kzrlxu7lzvnmsooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

#[bench]
#[inline(never)]
fn getargs4_short_cluster(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_SHORT_CLUSTER));
}

#[bench]
#[inline(never)]
fn getargs5_short_cluster(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_SHORT_CLUSTER.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_short_cluster(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_SHORT_CLUSTER_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_short_cluster(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_SHORT_CLUSTER.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_short_cluster(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_SHORT_CLUSTER_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_short_cluster(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_SHORT_CLUSTER.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_SHORT_EVALUE: [&str; 1000] =
    ["-rjryets8kzrlxu7lzvnmso4oiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

pub const ARGS_SHORT_EVALUE_BYTES: [&[u8]; 1000] =
    [b"-rjryets8kzrlxu7lzvnms4ooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

#[bench]
#[inline(never)]
fn getargs4_short_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_SHORT_EVALUE));
}

#[bench]
#[inline(never)]
fn getargs5_short_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_SHORT_EVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_short_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_SHORT_EVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_short_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_SHORT_EVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_short_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_SHORT_EVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_short_evalue(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_SHORT_EVALUE.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_SHORT_IVALUE: [&str; 1000] =
    ["-rjryets8kzrlxu7lzvnmsooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k4"; 1000];

pub const ARGS_SHORT_IVALUE_BYTES: [&[u8]; 1000] =
    [b"-rjryets8kzrlxu7lzvnmsooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k4"; 1000];

#[bench]
#[inline(never)]
fn getargs4_short_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_SHORT_IVALUE));
}

#[bench]
#[inline(never)]
fn getargs5_short_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_SHORT_IVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_short_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_SHORT_IVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_short_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_SHORT_IVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_short_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_SHORT_IVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_short_ivalue(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_SHORT_IVALUE.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_LONG_EVALUE: [&str; 1000] =
    ["--val1=rjryets8kzrlxu7lzvnms4ooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

pub const ARGS_LONG_EVALUE_BYTES: [&[u8]; 1000] =
    [b"--val1=rjryets8kzrlxu7lzvnms4ooiac8u9lxluphwrfudxaitfdomtce78grull9cpcvk7lyi07mdoclybtolssg7w7kwei79k"; 1000];

#[bench]
#[inline(never)]
fn getargs4_long_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_LONG_EVALUE));
}

#[bench]
#[inline(never)]
fn getargs5_long_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_LONG_EVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_long_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_LONG_EVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_long_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_LONG_EVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_long_evalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_LONG_EVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_long_evalue(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_LONG_EVALUE.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}

pub const ARGS_LONG_IVALUE: [&str; 1000] = ["--val1"; 1000];
pub const ARGS_LONG_IVALUE_BYTES: [&[u8]; 1000] = [b"--val1"; 1000];

#[bench]
#[inline(never)]
fn getargs4_long_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs4(&ARGS_LONG_IVALUE));
}

#[bench]
#[inline(never)]
fn getargs5_long_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5(ARGS_LONG_IVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargs5b_long_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargs5b(ARGS_LONG_IVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsL_long_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsL(ARGS_LONG_IVALUE.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLb_long_ivalue(bencher: &mut Bencher) {
    bencher.iter(|| getargsLb(ARGS_LONG_IVALUE_BYTES.iter().copied()));
}

#[bench]
#[inline(never)]
fn getargsLo_long_ivalue(bencher: &mut Bencher) {
    let args_os: Vec<&OsStr> = ARGS_LONG_IVALUE.iter().copied().map(AsRef::as_ref).collect();
    bencher.iter(|| getargsLo(args_os.iter().copied()));
}
