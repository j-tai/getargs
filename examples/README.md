# `getargs` examples

The following example shows what your app's code will generally look like. You
can use it as a reference, or copy it into your project.

1. [`complete.rs`](./complete.rs): a complete example that all argument
   information into a struct, including subcommands, subcommand-specific
   options, and repeated options.

The following examples show the features of `getargs` in more detail. You can
play with these to learn more about how `getargs` works.

2. [`print.rs`](./print.rs): an example that prints arguments as they are
   parsed. Includes short and long flags and optional and required values.
3. [`subcommands.rs`](./subcommands.rs): a basic example showing how to parse
   subcommands with their own specific options
4. [`no_alloc.rs`](./no_alloc.rs): shows how to use `argv` to avoid allocating
   on Unix (but not on Windows)
5. [`anywhere.rs`](./anywhere.rs): shows how to support passing options after
   and in-between positional arguments, rather than just at the beginning
