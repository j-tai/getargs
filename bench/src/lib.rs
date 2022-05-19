#![feature(test)]

extern crate test;

/// Compares the performance of `getargs` to other crates in the Rust
/// ecosystem, like `clap`, `getopt`/`getopts`, `lexopt` and more.
///
/// `cargo bench -- versus`
#[cfg(test)]
mod versus;

/// Compares the performance of current `getargs` to historical versions
/// to show either performance improvements or performance regressions.
///
/// `cargo bench -- evolution`
#[cfg(test)]
mod evolution;

pub const ARGS: [&str; 12] = [
    "-1",         // short_present1
    "-3",         // short_present3
    "--present1", // long_present1
    "--present3", // long_present3
    "-4",         // short_value1
    "value1",
    "-6", // short_value3
    "value3",
    "--val1", // long_value1
    "value1",
    "--val2", // long_value3
    "value2",
];

pub const ARGS_BYTES: [&[u8]; 12] = [
    b"-1".as_slice(), // short_present1
    b"-3",            // short_present3
    b"--present1",    // long_present1
    b"--present3",    // long_present3
    b"-4",            // short_value1
    b"value1",
    b"-6", // short_value3
    b"value3",
    b"--val1", // long_value1
    b"value1",
    b"--val2", // long_value3
    b"value2",
];
