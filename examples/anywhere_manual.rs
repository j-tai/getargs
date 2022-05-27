//! This example shows how to implement argument parsing in such a way
//! that flags can be provided anywhere, even after positional
//! arguments. `getargs` makes this relatively easy.
//!
//! Try it with arguments like: `x -r hi y -ohi z -- --not-a-flag`
//!
//! You will get:
//!
//! ```text
//! positional: "x"
//! option Short('r'): Ok("hi")
//! positional: "y"
//! option Short('o'): Some("hi")
//! positional: "z"
//! positional: "--not-a-flag"
//! ```

use getargs::{Opt, Options};
use std::env::args;

fn main() {
    let args = args().skip(1).collect::<Vec<_>>();
    let mut opts = Options::new(args.iter().map(String::as_str));

    while !opts.is_empty() {
        // First parse as many options as possible...
        while let Some(opt) = opts.next().expect("argument parsing error") {
            match opt {
                Opt::Short('o') | Opt::Long("optional") => {
                    eprintln!("option {:?}: {:?}", opt, opts.value_opt());
                }

                Opt::Short('r') | Opt::Long("required") => {
                    eprintln!("option {:?}: {:?}", opt, opts.value());
                }

                _ => eprintln!("option: {:?}", opt),
            }
        }

        // Then consume either one positional argument, or all if `--`
        while let Some(arg) = opts.arg() {
            eprintln!("positional: {:?}", arg);

            // If options haven't been ended, we are only guaranteed one
            // positional argument - there may be more flags here.
            if !opts.opts_ended() {
                break;
            }
        }
    }
}
