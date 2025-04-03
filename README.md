temp-env
========

Set environment variables temporarily.

This crate is useful for testing with different environment variables that should not interfere when running `cargo test`.

This code started as a small test helper written by [@fabian-braun] and [@nbaztec] and published by [@fabian-braun]
on [StackOverflow]. [@vmx] found it useful and took the time to make it a proper crate.

Examples
--------

```rust
temp_env::with_var("MY_ENV_VAR", Some("production"), || {
    // Run some code where `MY_ENV_VAR` is set to `production`.
});


temp_env::with_vars(
    [
        ("FIRST", Some("Hello")),
        ("SECOND", Some("World!")),
    ],
    || {
        // Run some code where `FIRST` is set to `Hello` and `SECOND` is set to `World!`.
    }
);

temp_env::with_vars(
    [
        ("FIRST", Some("Hello")),
        ("SECOND", None),
    ],
    || {
        // Run some code where `FIRST` is set to `Hello` and `SECOND` is unset (even if
        // it was set before)
    }
);

let value = temp_env::with_var("MY_ENV_VAR", Some("production"), || {
    // Compute a value in a closure while `MY_ENV_VAR` is set to `production`.
    let envvar = env::var("MY_ENV_VAR").unwrap();
    if envvar == "production" {
        true
    } else {
        false
    }
});
```

How does it work?
-------

This crate sets and unsets environment variables for the currently running (Rust) process. 
It leverages [`std::env::set_var`].

The provided functions `temp_env::with_*` provide the following features:
- Avoid interference when running concurrently
- Reset previously set env variables back to their original value upon completion, also in case of panic
- Temporarily unsetting env variables

Note that the crate makes use of a singleton mutex to avoid side effects between concurrently running tests.
This may impact the degree of concurrency in your test execution.

Features
--------

 - `async_closure`: When enabled you can use `async_with_var()` with async closures. This feature needs at least Rust version 1.64.

Noteworthy
----------

As an alternative to using this crate,
you might consider migrating your testing to [`cargo-nextest`](https://github.com/nextest-rs/nextest).
`cargo-nextest` runs each test in a separate process, which makes it unnecessary to synchronize the altering of environment variables
as described [here](https://nexte.st/docs/configuration/env-vars/#altering-the-environment-within-tests).

License
-------

This project is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE]) or https://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT] or https://opensource.org/licenses/MIT)

at your option.


[StackOverflow]: https://stackoverflow.com/questions/35858323/how-can-i-test-rust-methods-that-depend-on-environment-variables/67433684#67433684
[@fabian-braun]: https://github.com/fabian-braun
[@nbaztec]: https://github.com/nbaztec
[@vmx]: https://github.com/vmx
[LICENSE-APACHE]: LICENSE-APACHE
[LICENSE-MIT]: LICENSE-MIT
[`std::env::set_var`]: https://doc.rust-lang.org/std/env/fn.set_var.html
