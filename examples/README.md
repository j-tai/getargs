# `getargs` examples

1. [`print.rs`](./print.rs): a basic example of how to parse arguments
   with `getargs`. Shows short and long flags, optional and required
   values, and how to implement `--help`.

2. [`no_alloc.rs`](./no_alloc.rs): historically, the first example ever
   created for `getargs`. Shows how to use `argv` to avoid allocating
   on Linux and Unix (but not on Windows).

3. [`anywhere_manual.rs`](./anywhere_manual.rs) and
   [`anywhere_helper.rs`](./anywhere_helper.rs): shows how to implement
   support for passing options after and in-between positional arguments
   (basically, anywhere).
