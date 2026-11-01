# Fibril

An experimental Idris-like language implemented in Idris 2, targeting a
quantitative De Morgan cubical core, C/JavaScript backends, and embedded profiles.

**Status:** experimental core infrastructure with erased ordinary type checking
and an ordinary runtime-usage prototype. No surface parser, cubical term checker,
compiler backend, or real-time guarantees are implemented.
See [checker scope and limits](docs/erased-checker.md).

## Build

Use the Idris 2 `pack` tool from this project directory:

```sh
pack build fibril
pack test fibril
./build/exec/fibril --help
```

`pack.toml` pins collection `nightly-260903`, which selects Idris 2
0.8.0 at commit `74b33730b6fea649b15e8d01ab099df9effcc7a0`.
Initial validation used pack commit `846a90d76d1d4c451484eb09773f11a9e2fd58f2`.
Pack itself is not installed or pinned by the project configuration.
A C toolchain and the collection's Scheme implementation are bootstrap
requirements; these are not Fibril backend choices.

Tests combine deterministic regressions with shrinking Hedgehog properties;
see the [testing guide](docs/testing.md).

Tests live in `test/src/Tests/`, with their own `test/tests.ipkg` depending
on `fibril`. Pack's test entry points to that package; tests are not included
in the compiler's source tree.

`make build` and `make test` wrap the pack commands. Direct `idris2 --build`
remains possible, but bypasses collection selection. Review and test collection
upgrades explicitly; do not use a floating collection for project builds.

See [examples](examples/README.md) for runnable bootstrap programs and clearly
labeled proposed Fibril scenarios, including proofs.

Build the browsable handbook with `make handbook`, or use `make serve-docs`
to browse at http://127.0.0.1:8000. It includes diagrams, a curated call graph,
linked source pages, API reference, and the full design record.
See [handbook prerequisites](docs/handbook.md).

Generate API documentation with `make docs` (`build/docs/index.html`);
use the matching Idris 2 compiler as explained in the
[documentation policy](docs/documentation-policy.md).

See [documentation](docs/README.md) and [first milestone](docs/milestone-01.md).
