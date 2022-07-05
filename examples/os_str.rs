use getargs::{Arg, Options};
use std::ffi::OsStr;

#[cfg(unix)]
fn main() {
    use std::os::unix::ffi::OsStrExt;

    let args: Vec<_> = std::env::args_os().skip(1).collect();

    let mut opts = Options::new(args.iter().map(|s| s.as_bytes()));

    while let Some(arg) = opts.next_arg().expect("usage error") {
        match arg {
            Arg::Short(b'f') | Arg::Long(b"file") => {
                let f = OsStr::from_bytes(opts.value().expect("usage error"));
                println!("file option: {f:?}");
            }
            Arg::Positional(pos) => {
                let pos = OsStr::from_bytes(pos);
                println!("positional: {pos:?}");
            }
            _ => println!("other: {arg:?}"),
        }
    }
}

#[cfg(not(unix))]
fn main() {
    eprintln("Only supported on Unix because UTF-16 is hard, sorry :(");
}
