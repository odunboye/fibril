# Host resource sessions and abnormal interpreter completion

Status: host lifetime management, now used by the dedicated
[checked resource runner](io-resource-execution.md), but not source handle creation. This prepares cleanup for an interpreter that can stop
before returning its normal ownership pair.

`Runtime.ScopedInput.withInputSession body` creates an opaque per-execution
registry and calls the trusted host callback with it. `openSessionInput session
path` opens a read-only lease and registers it immediately on successful return.
The existing `readScopedInput` and `closeScopedInput` operations apply to it.

When the callback returns any represented value—including an interpreter error—
the session is revoked before all registered leases are released, newest first.
The function returns the primary value alongside a list of cleanup errors, rather
than replacing one error with another or stopping cleanup after the first error.
Explicitly closed leases are not closed a second time. Escaped leases reject
reads, and an escaped session rejects further opens with `FileSessionClosed`.
Both constructors and the raw underlying files remain inaccessible to clients.

Lease state now retains the first close outcome. If an explicit close fails and
automatic cleanup later visits that lease, cleanup reports the stored failure
without retrying `fclose`: an indeterminate close might already have released a
descriptor that the OS can reuse. A later explicit close still reports that the
lease is closed.

This registry is sequential, not atomic or thread-safe. It does not catch host
exceptions, allocation failures, divergence or process termination. Acquisition
and registration are not a crash-atomic transaction. Raw host callbacks remain
trusted and may themselves perform other effects. No source-level region token,
native handle registry or world-token guarantee is supplied by this module.

## Evidence

Six real-file session checks cover reads, cleanup after actual interpreter request
exhaustion, escaped sessions, multiple leases, explicit close and acquisition
failure. The earlier generic scope tests retain body/cleanup-error coverage.
Compile-negative checks verify opacity of both lease and session constructors.

## Next integration gate

The dedicated resource runner now connects checked core scopes to session-backed
execution, introduces internal region/handle references and validates ownership
return. Hosted [ownership-returning reads](io-owned-file-reads.md) now check live
reference generations. A [native resource runtime](io-native-resources.md) now
has direct cleanup tests; checked emission and differential validation remain. Current source file operations stay
disabled until those gates are tested.
