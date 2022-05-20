# `bench`

This is an internal crate that is used to run performance tests on
`getargs` and against other crates in the ecosystem. It is the crate
that [@LoganDark](https://github.com/LoganDark) used to optimize
[PR #4](https://github.com/j-tai/getargs/pull/4).

It is used for:

- Profiling `getargs` for optimization purposes
- Comparing different versions/branches (i.e. regression testing)
- Comparing `getargs` between other crates in the ecosystem

Currently:

- There are no big optimization targets for `getargs`. Low-hanging fruit
  such as function inlining have already been picked.
- `getargs` `0.5.0` is a consistent 25-50% improvement over `0.4.1`.
- `getargs` is at least one of the fastest argument parsing crates.
  Every other crate benchmarked here is significantly slower. If you
  find one that is faster, feel free to open a PR!

## Benching `getargs` itself

Get a nightly compiler, run `cargo bench -- evolution`. This will
benchmark the current version of `getargs` (`getargs5` and `getargs5b`)
against an old version of `getargs` (`getargs4`).

If you want to benchmark only `getargs5`, you can use
`cargo bench -- evolution::getargs5` for both string and bytes tests, or
`cargo bench -- evolution::getargs5_` for only string tests. You should
do this before and after adding a feature to see if performance changes.
Performance regressions will be reviewed on a case-by-case basis; it is
not a huge priority due to `getargs`' already-ridiculous speed, but it
is a secondary concern.

## Benching `getargs` against other crates

`cargo bench -- versus` will run benches against both `getargs` itself
(and version `0.4.1`, `getargs4`) and some other crates in the ecosystem
(`clap`, `pico-args`, `getopts`, `getopt`, and `lexopt` as of writing).

`getargs` should be the fastest by a considerable margin in both release
and dev mode; if it is not, feel free to open an issue asking about it.

## Profiling `getargs`

The `vs` example is the best for profiling `getargs` against `getargs4`.
There are a couple other examples for other stuff that was being messed
with at some point. Generally, look at the example you'll be running to
see if it'll work for your use case. Since you're using a profiler, you
should know what you're doing.
