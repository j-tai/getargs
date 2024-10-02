use getargs::{Arg, Argument, Options};
use std::ffi::OsString;
use std::path::PathBuf;

fn main() {
    let args: Vec<_> = std::env::args_os().skip(1).collect();

    let mut opts = Options::new(args.iter().map(OsString::as_os_str));

    while let Some(arg) = opts.next_arg().expect("usage error") {
        match arg {
            Arg::Short('f') | Arg::Long("file") => {
                let f = PathBuf::from(opts.value().expect("usage error"));
                println!("file option: {f:?}");
            }
            Arg::Positional(pos) => {
                println!("positional: {}", Argument::display(pos));
            }
            _ => println!("other: {}", arg),
        }
    }
}
