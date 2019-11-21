# getargs

An argument parser that is truly zero-cost, similar to getopts.

Example usage:

```rust
use std::process;
use getargs::{Error, Opt, Options, Result};

// You are recommended to create a struct to hold your arguments
#[derive(Default, Debug)]
struct MyArgsStruct<'a> {
    attack_mode: bool,
    suppress_bees: bool,
    em_dashes: bool,
    execute: &'a str,
}

fn parse_args<'a>(opts: &'a Options<'a>) -> Result<MyArgsStruct<'a>> {
    let mut res = MyArgsStruct::default();
    while let Some(opt) = opts.next() {
        match opt? {
            // -a or --attack
            Opt::Short('a') | Opt::Long("attack") => res.attack_mode = true,
            // -b
            Opt::Short('b') => res.suppress_bees = true,
            // Unicode short options are supported
            Opt::Short('\u{2014}') => res.em_dashes = true,
            // -e EXPRESSION, or -eEXPRESSION, or
            // --execute EXPRESSION, or --execute=EXPRESSION
            Opt::Short('e') | Opt::Long("execute") => res.execute = opts.arg()?,
            // An unknown option was passed
            opt => return Err(Error::UnknownOpt(opt)),
        }
    }
    Ok(res)
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let opts = Options::new(&args);
    let options = match parse_args(&opts) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("usage error: {}", e);
            process::exit(1);
        }
    };
    println!("{:#?}", options);
}
```

## Features

* Zero cost
* Zero copy
* Zero unsafe code
* Zero dependencies
* Simple to use yet versatile

## License

[MIT.](LICENSE)
