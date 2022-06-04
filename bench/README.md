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
  Every other crate benchmarked here is significantly slower, with the
  notable exception of `gumdrop`, which is only slightly slower. If you
  find one that is faster, feel free to open a PR!

## Benching `getargs` itself

Get a nightly compiler, run `cargo bench -- evolution`. This will
benchmark the current version of `getargs` (`getargs5`, `getargs5b`,
`getargsL` and `getargsLb`) against an old version, `getargs4`.

`getargsL` and `getargsLb` are the current version; `getargs5` and
`getargs5b` are the `master` branch of the upstream repository; and
`getargs4` is version `0.4.1` from the upstream repository.

If you want to benchmark only `getargsL`, you can use
`cargo bench -- evolution::getargsL` for both string and bytes tests, or
`cargo bench -- evolution::getargsL_` for only string tests. You can
also do `cargo bench -- evolution::getargs5_ evolution::getargsL_` to
compare the string versions of what you have locally and what is
upstream, to make sure that you aren't creating a regression.
Performance regressions will be reviewed on a case-by-case basis; it is
not a huge priority due to `getargs`' already-ridiculous speed, but it
is a secondary concern.

## Benching `getargs` against other crates

`cargo bench -- versus` will run benches against both `getargs` itself
(and version `0.4.1`, `getargs4`) and some other crates in the ecosystem
(`clap`, `pico-args`, `getopts`, `getopt`, `lexopt`, `structopt` and
`gumdrop` as of writing).

`getargs` should be the fastest by a considerable margin in both release
and dev mode, except against `gumdrop` which is fairly competitive; if
it is not, feel free to open an issue asking about it.

## Profiling `getargs`

The `versus` example is the best for profiling `getargs` against
`getargs4`. There are a couple other examples for other stuff that was
being messed with at some point. Generally, look at the example you'll
be running to see if it'll work for your use case. Since you're using a
profiler, you should know what you're doing.
