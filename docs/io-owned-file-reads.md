# Ownership-returning hosted file reads

Status: checked core read operation and hosted execution. A
[trusted native resource runtime](io-native-resources.md) now has direct tests;
checked native resource emission and source file primitives remain disabled.

## Core operation

`ReadInputFile handle` requires `handle : FileHandle region` and describes:

```text
IO (OwnedPair (FileHandle region) ReadResult)
```

Both pair fields are linear. The input handle is consumed once; its successor is
returned even when the represented result is EOF or an input error. The existing
ReadResult alternatives remain EOF, line and error String. Full/head conversion
performs no file reads. No source name exposes this operation yet.

A region-polymorphic scope callback can return `ReadInputFile handle` directly
when its ordinary result type is ReadResult. This satisfies the scope's
ownership-returning signature without discarding the read outcome.

## Live-reference checking

Internal `FileHandleValue identity generation` references retain one region
identity while advancing their runtime generation. Generations do not change
the handle's type, but do distinguish its operational value. Caller syntax still
cannot contain references, including in erased positions.

`Runtime.InputOwnership` is an opaque sequential table over registered host
leases. It rejects unknown, stale and revoked references before performing a
read. A valid read consumes its generation before calling the host adapter;
line/EOF/represented read failure returns a successor. Observing an already
closed lease revokes the entry and produces an interpreter reference failure,
not a fresh usable handle. Scope exit checks the returned ID and live generation,
revokes the entry and closes the original lease. Session cleanup remains the
backstop for represented interpreter failures.

Table checks are runtime defense in depth, not a replacement for quantity-1
source bindings or a proof of quantitative preservation. The table does not own
physical close and is not thread-safe; trusted code must use it with session
cleanup. Identities are local to a run, and the closed Unit entry boundary plus
reference admission prevents source references being supplied across runs.

## Input and failure behavior

The hosted adapter uses the existing LF/CRLF, EOF and Unicode behavior, with a
post-decoding 8192-character limit in the resource runner. Overlong lines have
already been consumed. Their represented error still carries successor ownership
and can be followed by another read. Unknown/stale/revoked references instead
stop interpretation; enclosing scopes still perform cleanup.

## Evidence and remaining work

Tests cover the checked callback type, inert reduction, static duplication
rejection, reference generations, unknown/stale/revoked reads, unchanged file
position after a stale read, continued ownership after read failure, EOF, closed
leases and real checked scopes reading/closing files. A compile-negative check
verifies that clients cannot construct the ownership table.

Native handle/pair representation, generation checks and scoped cleanup now
have direct runtime tests. Next implement checked resource emission and
hosted/native differential tests before exposing source scoped-file APIs.
This is not world-token IO, general exception-safe cleanup, an OS sandbox or a
verified backend.
