# Scoped input-file ownership: first pilot

Status: host-only implementation and tests. A separate
[abstract source handle type](io-static-handles.md) now has typing tests, but no
source open/read/close primitive or native handle value exists.

## Implemented host boundary

`Runtime.ScopedInput` exports an opaque `ScopedInput` type, not its constructor,
raw `File` or lease state. `withScopedInput path body` acquires a read-only file,
invokes a trusted host callback and performs cleanup after its represented
return, whether that return is success or failure.

`readScopedInput limit lease` uses the existing line/EOF/error rules.
`closeScopedInput lease` allows explicit close inside a scope. Repeated explicit
close and reads after close return `FileLeaseClosed`. Returning the wrapper from
the callback is possible in host Idris, but scope cleanup revokes it; subsequent
reads fail without accessing the closed file. This is runtime lifetime checking,
not static linearity or a thread-safe concurrent lease.

Close uses checked C `fclose`, not the host API that discards its return status.
The lease is revoked before calling close, even on failure: retrying an
indeterminate close could affect a reused descriptor. Automatic scope cleanup
returns a revoked lease's stored close outcome rather than closing twice.
A [host resource session](io-resource-session.md) now tracks multiple leases and
cleans up on represented interpreter failure before normal ownership return.

`Effect.Resource.ResourceOutcome error value` distinguishes acquisition failure
from a body result paired with a cleanup result. The generic host seam
`Runtime.Resource.runResourceScope` preserves both body and cleanup failures,
and a successful body value alongside a cleanup failure. Opening failure invokes
neither callback nor cleanup.

Cleanup is guaranteed only after represented callback returns. Nontermination,
backend exceptions, allocation failure and process termination are not caught.
The callback is trusted host code and can ignore errors or diverge. No OS
sandbox, FFI memory-safety or exactly-once external-effect claim follows.

## Proposed source protocol — not implemented

A plain callback `Handle -> IO A` is insufficient: it permits returning a handle
inside A, losing it on an error branch, or selecting an unrestricted closure that
captures ownership. A runtime lease guard alone does not satisfy the requested
source-level rejections.

The scoped source design should use:

1. An unforgeable `Handle region` type created only at a trusted open boundary.
2. A fresh abstract region under the callback, preventing handles from different
   nested scopes being substituted for one another.
3. A linear input handle and an ownership-returning result, conceptually
   `IO (OwnedPair (Handle region) A)`, on every represented body path.
4. Read operations that consume a handle and return its successor alongside an
   explicit line/EOF/error result, including on represented read failure.
5. Cleanup at the scope boundary after recovering ownership. A scoped callback
   does not get an independent source `close` that consumes its only handle and
   then somehow returns the same live token; manual close needs a separate
   closed-state protocol or a later manual-ownership API.
6. A callback permission that cannot capture arbitrary linear ambient resources
   if open failure skips that callback. An initial unrestricted callback is
   restrictive but avoids silently losing such captures.

Fresh regions alone do not prevent existential escape through A. The mandatory
linear return of ownership is also necessary: the same handle cannot be both
returned to the scope for cleanup and packed into A. A complete source design
must check this through dependent pairs, erased arguments, nested scopes and
closures before exposing the primitives. These sketches are not checked source
signatures or a proof of resource safety.

## Tests and next gates

The focused hosted suite adds five injected scope tests and six real-file lease
tests. They cover success, acquisition failure, body/cleanup failures, escaped
leases, double close and use-after-close. A separate compile-negative check
verifies that a host client cannot access the raw lease constructor.

Abstract handle formation and the [inert ownership-returning core
boundary](io-core-scope.md) now have typing regressions, including nested regions
and existential escape. A [dedicated checked hosted runner](io-resource-execution.md)
now introduces scope handles and checks their ownership return. Hosted
[ownership-returning reads](io-owned-file-reads.md) now validate live generations.
Next implement corresponding native registry/cleanup tests. Keep source file
primitives disabled until those gates pass. Console IO remains unchanged.
