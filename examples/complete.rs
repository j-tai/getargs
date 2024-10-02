use getargs::{Error, Opt, Options};
use std::process::exit;
use thiserror::Error;

#[derive(Error, Debug)]
enum UsageError<'a> {
    /// Early return due to --help
    #[error("--help was specified")]
    Help,
    /// Error from getargs
    #[error("{0}")]
    Getargs(getargs::Error<'a, &'a str>),
    #[error("unknown option {0}")]
    UnknownOption(Opt<'a>),
    #[error("unknown subcommand {0:?}")]
    UnknownSubcommand(&'a str),
    #[error("missing subcommand")]
    MissingSubcommand,
}

impl<'a> From<getargs::Error<'a, &'a str>> for UsageError<'a> {
    fn from(e: Error<'a, &'a str>) -> Self {
        UsageError::Getargs(e)
    }
}

#[allow(unused)] // fields are not actually used in this example
#[derive(Debug)]
struct Arguments<'a> {
    verbosity: u32,
    subcommand: Subcommand<'a>,
}

#[allow(unused)] // fields are not actually used in this example
#[derive(Debug)]
enum Subcommand<'a> {
    Create {
        output: Option<&'a str>,
        args: Vec<&'a str>,
    },
    Delete {
        backup: Option<&'a str>,
        args: Vec<&'a str>,
    },
}

/// Parse all the arguments
fn parse_args<'a, I: Iterator<Item = &'a str>>(
    opts: &mut Options<'a, &'a str, I>,
) -> Result<Arguments<'a>, UsageError<'a>> {
    let mut verbosity = 0;

    // Parse the top-level options
    while let Some(opt) = opts.next_opt()? {
        match opt {
            Opt::Short('h') | Opt::Long("help") => return Err(UsageError::Help),
            Opt::Short('v') | Opt::Long("verbose") => verbosity += 1,
            _ => return Err(UsageError::UnknownOption(opt)),
        }
    }

    let subcommand_name = opts
        .next_positional()
        .ok_or(UsageError::MissingSubcommand)?;
    let subcommand = match subcommand_name {
        "c" | "create" => parse_create_args(opts)?,
        "d" | "delete" => parse_delete_args(opts)?,
        _ => return Err(UsageError::UnknownSubcommand(subcommand_name)),
    };

    Ok(Arguments {
        verbosity,
        subcommand,
    })
}

/// Parse the arguments for the 'create' subcommand
fn parse_create_args<'a, I: Iterator<Item = &'a str>>(
    opts: &mut Options<'a, &'a str, I>,
) -> Result<Subcommand<'a>, UsageError<'a>> {
    let mut output = None;
    while let Some(opt) = opts.next_opt()? {
        match opt {
            Opt::Short('o') | Opt::Long("output") => output = Some(opts.value()?),
            _ => return Err(UsageError::UnknownOption(opt)),
        }
    }

    let args = opts.positionals().collect();
    Ok(Subcommand::Create { output, args })
}

/// Parse the arguments for the 'delete' subcommand
fn parse_delete_args<'a, I: Iterator<Item = &'a str>>(
    opts: &mut Options<'a, &'a str, I>,
) -> Result<Subcommand<'a>, UsageError<'a>> {
    let mut backup = None;
    while let Some(opt) = opts.next_opt()? {
        match opt {
            Opt::Short('b') | Opt::Long("backup") => {
                backup = Some(opts.value_opt().unwrap_or(".bak"))
            }
            _ => return Err(UsageError::UnknownOption(opt)),
        }
    }

    let args = opts.positionals().collect();
    Ok(Subcommand::Delete { backup, args })
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let mut opts = Options::new(args.iter().map(String::as_str));
    let arguments = parse_args(&mut opts);
    match arguments {
        Ok(a) => println!("{a:#?}"),
        Err(UsageError::Help) => {
            println!(
                r"Usage: complete [-h] [-vvvv] SUBCOMMAND
Argument parsing demo. This does not actually create or delete anything.

Options:
    -h, --help      help
    -v, --verbose   verbose (specify multiple times for more verbosity)

SUBCOMMAND is one of:
    create [-o OUTPUT] [FILE ...]
    delete [-b[SUFFIX]] [FILE ...]"
            );
        }
        Err(e) => {
            println!("Usage error: {e}");
            println!("Try '--help' for help");
            exit(1);
        }
    }
}
