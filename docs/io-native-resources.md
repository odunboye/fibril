# Native scoped-resource runtime

Status: trusted C runtime, direct adversarial tests and
[checked resource emission](io-resource-emission.md) with differential tests.
Source scoped-file primitives remain disabled. Existing console-only native
entry points reject resource requests without opening files.

## Runtime boundary

`fibril_native_resource_run` is the explicit incremental resource entry point.
`f_with_input` describes acquisition plus a region-polymorphic body; `f_read_input`
describes an ownership-returning read. Neither constructor itself opens files.
The callback's region argument is erased, and no public C constructor supplies
live handle values to generated source programs.

The resource runtime creates a per-run file registry. Each handle carries an
identity and generation. Reads reject unknown, revoked and stale references
before touching the file, then advance the generation and return an owned pair
of the successor handle and the existing EOF/line/error variant. Scope completion
requires its own current handle and preserves the body's ordinary result.

Paths are length-delimited until acquisition and reject embedded NUL before
conversion to C filenames. Open failure is a represented scope result and skips
the body. Open-error wording is not promised to match every host platform.

Native pairs carry two lazy fields with explicit erasure flags; pair elimination
uses ordinary closure application. Scope ownership and read-result pairs retain
both fields. Checked resource emission derives erasure flags from the checked Sigma
annotation. Direct C fixture success alone is not typing evidence.

## Cleanup and budgets

Reads, writes and open attempts share request fuel. Mandatory close does not
consume it. A registry entry is installed before evaluating the body. Scope exit
revokes the file before fclose and retains any close error without retrying the
stream. A nonallocating final registry walk closes remaining live files, newest
first, even after represented allocation/evaluation/request failure.

Primary errors and every retained cleanup error are reported separately. A
cleanup failure with a successful A result also supplies A plus its error to the
scope continuation; the final C process still fails if any registry cleanup error
is retained. This is the conservative counterpart of the hosted runner returning
cleanup failures independently of its primary outcome.

Earlier output can remain after failure. Signals, process termination, foreign
memory faults and arbitrary C longjmp/exception behavior are not caught. The
registry is sequential, not thread-safe or a sandbox.

## Validation

`make -j8 io-resource-runtime-test` runs 25 trusted-C tests. They cover acquisition,
current/stale/revoked ownership, successor reads, EOF, read errors, nested scopes,
region swaps, malformed ownership returns, erased pair fields, NUL paths,
NUL text read/write rejection, partial output and cleanup after request/evaluation/allocation exhaustion.
Open/close counters check that other runners perform no acquisition and that
cleanup never closes an acquired stream twice. fclose injection calls the real
close first and then changes its status; it tests represented error handling,
not a real OS close failure.

The suite also passes with:

```sh
make -j8 io-resource-runtime-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

These fixtures intentionally bypass checking and sometimes violate linearity to
exercise defensive runtime failures. A separate 29-case checked-core
[hosted/native differential suite](io-resource-emission.md) now covers resource
emission, ownership threading, text boundaries and represented failures.
Existing output and console-only emission retains its resource gates.
