# Checked scoped ownership boundary

Status: inert core syntax and typing rules, not executable file IO or a source
scope primitive. Existing hosted lease tests are a separate implementation slice.

## Core shape

`WithInputFile A path body` describes a read-only scope. Its typing rule requires:

- `A : Type 0`;
- `path : String`;
- a body with the conceptual type below (the pair notation is explanatory, not
  new source syntax):

```text
(0 region : Type 0) ->
(1 handle : FileHandle region) ->
IO (OwnedPair (FileHandle region) A)
```

`OwnedPair` here means the existing Sigma with quantity 1 on both fields. The
body must return ownership under its own abstract region, not a different
region, alongside its ordinary result. A source `close` primitive that destroys
that ownership is not part of this protocol.

The result is `IO (fileScopeResultType A)`, a finite variant:

- tag 0: open failure, linear String payload;
- tag 1: successful A result, linear payload;
- tag 2: A result plus cleanup-error String, both linear pair fields.

Application failures can be represented inside A. Interpreter failures before A
exists require a separate cleanup/error path; these rules do not implement it.

## Callback capture and escape

Opening can fail without calling the body. Runtime usage therefore scales the
body's ambient demand by unrestricted permission: captured linear resources
cannot be silently lost by a skipped callback. The handle introduced inside the
body remains linear and must be returned once.

Nested body region variables are distinct during checking. Returning an outer
handle as the inner scope's ownership fails type comparison. Returning the same
handle both for cleanup and inside an existential result fails usage checking.
The existential package itself lives in Type1, above this first scope API's
Type0 result bound, so its negative usage regression checks the body directly;
it first verifies erased typing to avoid mistaking a universe error for evidence
of ownership checking.

## Non-execution boundary

Full and head reduction never open files. Full normalization may compute inside
the description's result annotation, path and body, as with other pure IO
syntax. Structural scope transport, renaming/substitution proofs and accounting
include every field.

A checked `IO Unit` program that consumes this scope's result is currently
rejected by both native emission modes and by hosted incremental interpretation,
before any scope request is exposed. No source primitive creates this syntax.
The tests intentionally enforce those gates until execution and cleanup exist.

## Evidence and remaining work

Fifteen checks cover valid ownership-returning callbacks, inert normalization,
missing ownership, existential duplication, skipped-callback capture, nested
region substitution, malformed paths/results and fail-closed execution.

Next: a trusted introduction boundary that creates fresh runtime regions and
maps handles to revocable host resources, implements ownership-returning reads,
and cleans up even if body interpretation fails before returning ownership.
Native execution must enforce the same lifetime/cleanup contract. Only then
expose scoped source primitives. This is not a subject-reduction proof,
exception-safe source resource implementation or world-token IO.
