# getargs

An argument parser that is truly zero-cost, similar to getopts.

## Features

* Short `-f` and long `--flag` flags
* Required implicit values `-i value` and `--implicit value`
* Required or optional explicit values `-eVALUE` and `--explicit=value`
* Positional arguments and `--`

## Benefits

* Zero cost
* Zero copy
* Zero unsafe code
* Zero dependencies
* Zero allocation
* Simple to use yet versatile
* `#![no_std]`-compatible
* Compatible with `&str` and `&[u8]` (`OsStr` requires manual conversion)

## Example

```rust
use std::process;
use getargs::{Opt, Options};
use std::str::FromStr;
use std::num::ParseIntError;

#[derive(Clone, Eq, PartialEq, Debug, thiserror::Error)]
enum Error<'str> {
    #[error("{0:?}")]
    Getargs(getargs::Error<&'str str>),
    #[error("parsing version: {0}")]
    VersionParseError(ParseIntError),
    #[error("unknown option: {0}")]
    UnknownOption(Opt<&'str str>)
}

impl<'arg> From<getargs::Error<&'arg str>> for Error<'arg> {
    fn from(error: getargs::Error<&'arg str>) -> Self {
        Self::Getargs(error)
    }
}

// You are recommended to create a struct to hold your arguments
#[derive(Default, Debug)]
struct MyArgsStruct<'str> {
    attack_mode: bool,
    em_dashes: bool,
    execute: &'str str,
    set_version: u32,
    positional_args: Vec<&'str str>,
}

fn parse_args<'a, 'str, I: Iterator<Item = &'str str>>(opts: &'a mut Options<&'str str, I>) -> Result<MyArgsStruct<'str>, Error<'str>> {
    let mut res = MyArgsStruct::default();
    while let Some(opt) = opts.next()? {
        match opt {
            // -a or --attack
            Opt::Short('a') | Opt::Long("attack") => res.attack_mode = true,
            // Unicode short options are supported
            Opt::Short('\u{2014}') => res.em_dashes = true,
            // -e EXPRESSION, or -eEXPRESSION, or
            // --execute EXPRESSION, or --execute=EXPRESSION
            Opt::Short('e') | Opt::Long("execute") => res.execute = opts.value()?,
            // Automatically parses the value as a u32
            Opt::Short('V') => res.set_version = u32::from_str(opts.value()?).map_err(Error::VersionParseError)?,
            // An unknown option was passed
            opt => return Err(Error::UnknownOption(opt)),
        }
    }
    res.positional_args = opts.args().collect();
    Ok(res)
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let mut opts = Options::new(args.iter().map(String::as_str));
    let options = match parse_args(&mut opts) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("error: {}", e);
            process::exit(1);
        }
    };
    println!("{:#?}", options);
}
```

## License

[MIT.](LICENSE)
