# Fibril

An experimental Idris-like language implemented in Idris 2, targeting a
quantitative De Morgan cubical core, C/JavaScript backends, and embedded profiles.

**Status:** bootstrap skeleton only. No Fibril parser, checker, cubical rules,
compiler backend, or real-time guarantees are implemented.

## Build

Initial tested toolchain: Idris 2 0.8.0-74b33730b.

Run `make build`, then `./build/exec/fibril --help`.
Run `make test` for bootstrap smoke tests.

See [documentation](docs/README.md) and [first milestone](docs/milestone-01.md).
