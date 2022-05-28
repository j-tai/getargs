//! This example shows an alternative way to implement parsing like
//! the `anywhere_manual` example that uses a helper function instead.
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

use getargs::{Argument, Opt, Options, Result};
use std::env::args;
use std::fmt::{Display, Formatter};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Arg<A: Argument> {
    Short(A::ShortOpt),
    Long(A),
    Positional(A),
}

impl<A: Argument> From<Opt<A>> for Arg<A> {
    fn from(opt: Opt<A>) -> Self {
        match opt {
            Opt::Long(long) => Self::Long(long),
            Opt::Short(short) => Self::Short(short),
        }
    }
}

impl<S: Display, A: Argument<ShortOpt = S> + Display> Display for Arg<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Short(short) => write!(f, "-{}", short),
            Self::Long(long) => write!(f, "--{}", long),
            Self::Positional(positional) => write!(f, "{}", positional),
        }
    }
}

pub fn next_arg<A: Argument, I: Iterator<Item = A>>(
    opts: &mut Options<A, I>,
) -> Result<A, Option<Arg<A>>> {
    if !opts.opts_ended() {
        if let Some(opt) = opts.next()? {
            return Ok(Some(opt.into()));
        }
    }

    Ok(opts.arg().map(Arg::Positional))
}

fn main() {
    let args = args().skip(1).collect::<Vec<_>>();
    let mut opts = Options::new(args.iter().map(String::as_str));

    while let Some(opt) = next_arg(&mut opts).expect("argument parsing error") {
        match opt {
            Arg::Short('o') | Arg::Long("optional") => {
                eprintln!("option {:?}: {:?}", opt, opts.value_opt());
            }

            Arg::Short('r') | Arg::Long("required") => {
                eprintln!("option {:?}: {:?}", opt, opts.value());
            }

            Arg::Short(_) | Arg::Long(_) => eprintln!("option: {:?}", opt),
            Arg::Positional(positional) => eprintln!("positional: {:?}", positional),
        }
    }
}
