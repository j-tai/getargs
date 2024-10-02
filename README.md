# getargs

An argument parser that is truly zero-cost, similar to Unix's `getopts`.

## About

`getargs` is a low-level, efficient and versatile argument parser that
works similarly to `getopts`. It works by producing a stream of options,
and after each option, your code decides whether to require and retrieve
the value for the option or not.

You don't have to declare a list of valid options up-front, so `getargs`
does not have to allocate space for them or spend runtime searching for
them. This also means that you have to write your own help message, but
since `--help` is just another flag, there are no restrictions on what
you do with it.

## Features

* Short `-f` and long `--flag` flags
* Required implicit values `-i VALUE` and `--implicit VALUE`
* Required or optional explicit values `-eVALUE` and `--explicit=VALUE`
* Positional arguments and `--`
* Parse options at the beginning of the argument list, or anywhere
* Optionally parse negative numbers as positional arguments

## Benefits

* Zero cost
* Zero copy
* Zero unsafe code except for `&OsStr`
* Zero dependencies
* Zero allocation
* Simple to use yet versatile
* `#![no_std]`-compatible except for `&OsStr`
* Compatible with `&str`, `&[u8]` and `&OsStr`

## Performance

`getargs` has had a lot of attention put into profiling and
optimization, and on a modern machine it takes under 0.2μs to parse a
short array of 12 arguments.

In our testing, `getargs` is faster than every other argument parsing
library on crates.io. Its closest competitor is `gumdrop`, which is only
~30% slower in the worst case, and its second-closest competitor is
`getopt`, which takes three times as long. Other libraries degrade
quickly; `clap` takes 45x longer. (This is not an entirely fair
comparison though, as `clap` is not just an argument-parsing library,
but an entire command-line application framework. It is perhaps
overqualified for simple tasks.)

## Example

For examples, see [the `examples` directory][./examples/] for small
programs that you can compile and run yourself to see how `getargs`
works.

## License

[MIT.](LICENSE)
