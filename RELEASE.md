Release process
===============

Create a pull request with a version bump to indicate the intention to do a release. This should give users the ability to give feedback, e.g. if a breaking change was missed and the version bump is incorrect.

Once that PR is merged do the actual release with [`cargo-release`](https://github.com/crate-ci/cargo-release).

This requires the following permissions

- on github.com/vmx/temp-env
  - creating tags
  - pushing to `main`
- on crates.io
  - publish access to all published crates

Dry run

```console
$ cargo release -vvv
```

Actual publishing

```console
$ cargo release --execute
```
