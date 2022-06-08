use getargs::{Opt, Options};
use std::env::args;

fn main() {
    let mut args = args().skip(1).collect::<Vec<_>>();

    if args.is_empty() {
        args.push(String::from("--help")); // help the user out :)
    }

    let mut opts = Options::new(args.iter().map(String::as_str));

    while let Some(opt) = opts.next_opt().expect("argument parsing error") {
        match opt {
            Opt::Short('h') | Opt::Long("help") => {
                eprintln!(
                    r"Usage: print.rs [OPTIONS] [ARGS]...
This example prints all options and positional arguments passed to it.
It also includes some short and long options that have a required or
optional value.

  -h, --help       display this help and exit
  -o, --optional   consume an optional value and print the result
  -r, --required   consume a required value and print it
  <anything else>  print the flag passed"
                );

                return;
            }

            Opt::Short('o') | Opt::Long("optional") => {
                eprintln!("option {:?}: {:?}", opt, opts.value_opt());
            }

            Opt::Short('r') | Opt::Long("required") => {
                eprintln!("option {:?}: {:?}", opt, opts.value());
            }

            _ => eprintln!("option: {:?}", opt),
        }
    }

    for arg in opts.positionals() {
        eprintln!("positional: {:?}", arg)
    }
}
