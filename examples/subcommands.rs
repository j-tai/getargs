use getargs::{Opt, Options, Result};
use std::env::args;

fn main() {
    let args = args().skip(1).collect::<Vec<_>>();
    let mut opts = Options::new(args.iter().map(String::as_str));

    parse(&mut opts).expect("argument parsing error");
}

fn parse<'arg, I: Iterator<Item = &'arg str>>(
    opts: &mut Options<'arg, &'arg str, I>,
) -> Result<'arg, &'arg str, ()> {
    while let Some(opt) = opts.next_opt()? {
        println!("option for base command: {opt}");
    }

    let subcommand = opts.next_positional();
    println!("subcommand: {subcommand:?}");
    match subcommand {
        None => println!("no subcommand"),
        Some("run") => parse_run(opts)?,
        Some("test") => parse_test(opts)?,
        Some(s) => println!("unknown subcommand {s:?}"),
    }
    Ok(())
}

fn parse_run<'arg, I: Iterator<Item = &'arg str>>(
    opts: &mut Options<'arg, &'arg str, I>,
) -> Result<'arg, &'arg str, ()> {
    while let Some(opt) = opts.next_opt()? {
        match opt {
            Opt::Short('r') | Opt::Long("release") => println!("release mode"),
            _ => println!("'run' subcommand got unknown option {opt:?}"),
        }
    }
    for pos in opts.positionals() {
        println!("positional arg: {pos}");
    }
    Ok(())
}

fn parse_test<'arg, I: Iterator<Item = &'arg str>>(
    opts: &mut Options<'arg, &'arg str, I>,
) -> Result<'arg, &'arg str, ()> {
    while let Some(opt) = opts.next_opt()? {
        match opt {
            Opt::Long("test") => {
                let name = opts.value()?;
                println!("testing {name}");
            }
            _ => println!("'test' subcommand got unknown option {opt:?}"),
        }
    }
    for pos in opts.positionals() {
        println!("positional arg: {pos}");
    }
    Ok(())
}
