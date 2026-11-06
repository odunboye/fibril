# Hosted checked resource execution

Status: dedicated hosted runner for checked core scopes, now compared against
[checked native resource emission](io-resource-emission.md). No source scope/file
operations are enabled yet. Output-only and console-interactive runners and
emitters retain their fail-closed scope gates.

## Trusted introduction boundary

`Driver.Resource.runResourceTermWith` first checks admission and a closed
`IO Unit` entry. Caller-supplied `FileHandleValue` references are forbidden
anywhere in the input syntax, including annotations and erased arguments.
Admission also applies the existing 8192-node and literal-payload limits.

On a successful scope open, a per-run counter supplies an internal region and
handle reference. The region is a nominal type with a reserved internal key;
source identifiers cannot name that key. Raw core syntax remains trusted, so
checking alone is not reference authorization: the entry admission gate is
load-bearing. IDs are fresh within a single run, not globally persistent names.
The execution result is Unit and escaped host leases are revoked at session exit.

The runner instantiates the checked region-polymorphic body with that region
and a generation-zero handle. [Ownership-returning reads](io-owned-file-reads.md)
now advance generations and reject stale/unknown/revoked references. After body interpretation it checks the ownership pair against the
expected region/type and explicitly checks the returned handle ID and live
generation before
releasing the corresponding lease. No raw host file pointer occurs in a term.

## Results and cleanup

Successful scope completion returns the existing finite variant: open failure,
successful A, or A plus cleanup error. A represented body-interpreter failure
still closes the lease; primary and close failures are preserved together.
The surrounding input session is a cleanup backstop and returns its cleanup
failures independently from the primary execution outcome.

Acquisition consumes one shared request allowance, including failed opens;
console reads and writes consume the same allowance. Mandatory file cleanup
never consumes request fuel. Description depth and reduction fuel are separate.
Earlier output may be visible before a later failure. Final stdout flushing is
checked on success. Host exceptions, allocation failure, divergence, signals and
process termination remain outside the represented cleanup guarantee.

Adapters and the optional lease observer are trusted host callbacks. Production
uses real console adapters and a no-op observer. Tests use the observer to verify
revocation and to inject an early-close state error, not a real OS fclose failure.

## Evidence and remaining gates

Eleven initial tests exercise real open/close, returned ownership, acquisition failure,
NUL-path rejection,
shared request and description-depth exhaustion, output failure, distinct nested
regions, primary plus cleanup-state errors, cleanup-result handling and rejection
of injected runtime references. Existing file/session tests separately cover
revocation, opacity and scope outcome preservation.

Ownership-returning file reads and live-reference checks now execute in the
hosted runner. A [native resource runtime](io-native-resources.md) now has
registration/cleanup tests and [checked emission](io-resource-emission.md) now
has 29 hosted/native cases. Source scope/file exposure remains a separate API,
capability and cleanup-contract gate. This runner is not a completed
linear-resource semantics, verified backend or world-token IO implementation.
