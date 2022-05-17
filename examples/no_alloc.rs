//! This example reads flags and position arguments without allocating in any way. The `argv` crate
//! is used to read from the program arguments without allocating (Unix-only) and since `Options`
//! now accepts an iterator, there is no need to create a slice in order to parse flags.
//!
//! Additionally, all strings and errors are annotated with the correct lifetimes, so that the
//! lifetime of the iterator itself does not matter so much anymore.

use getargs::{Opt, Options};

fn main() {
    let args = argv::iter().skip(1).map(|os| {
        os.to_str()
            .expect("argument couldn't be converted to UTF-8")
    });

    let mut opts = Options::new(args);

    while let Some(opt) = opts.next().expect("calling Options::next") {
        match opt {
            Opt::Short('v') | Opt::Long("value") => eprintln!("'{}': {:?}", opt, opts.value()),
            Opt::Short('o') | Opt::Long("opt") => eprintln!("'{}': {:?}", opt, opts.value_opt()),
            _ => eprintln!("'{}'", opt),
        }
    }

    for positional in opts.args() {
        eprintln!("positional argument: {}", positional);
    }
}
