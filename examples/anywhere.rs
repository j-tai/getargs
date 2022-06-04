//! This example shows how to use the `Options::next_arg` method to
//! accept options and positional arguments anywhere.
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

use getargs::{Arg, Options};
use std::env::args;

fn main() {
    let mut args = args().skip(1).collect::<Vec<_>>();

    if args.is_empty() {
        args.push(String::from("--help")); // help the user out :)
    }

    let mut opts = Options::new(args.iter().map(String::as_str));

    while let Some(arg) = opts.next_arg().expect("argument parsing error") {
        match arg {
            Arg::Short('h') | Arg::Long("help") => {
                eprintln!(
                    r"Usage: anywhere.rs [OPTIONS/ARGS]...
This example prints all options and positional arguments passed to it,
but options and positional arguments can be passed anywhere. It also
includes some short and long options that have a required or optional
value, just like print.rs.

  -h, --help       display this help and exit
  -o, --optional   consume an optional value and print the result
  -r, --required   consume a required value and print it
  <anything else>  print the flag passed"
                );

                return;
            }

            Arg::Short('o') | Arg::Long("optional") => {
                eprintln!("option {:?}: {:?}", arg, opts.value_opt());
            }

            Arg::Short('r') | Arg::Long("required") => {
                eprintln!("option {:?}: {:?}", arg, opts.value());
            }

            Arg::Short(_) | Arg::Long(_) => eprintln!("option: {:?}", arg),
            Arg::Positional(arg) => eprintln!("positional: {:?}", arg),
        }
    }
}
