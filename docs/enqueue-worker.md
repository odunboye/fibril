# Checked enqueue worker: validate, commit, then acknowledge

Status: implemented **local enqueue demonstration**, not an authenticated network
service or email worker. It connects checked Fibril request validation, bounded
binary embedding and the optional SQLite store. No SMTP dispatch is performed.

## Request v1

A request is one complete bounded binary message:

| Offset | Size | Meaning |
| --- | --- | --- |
| 0 | 4 | ASCII `FQ01`, exact version/magic |
| 4 | 16 | Opaque idempotency key |
| 20 | 1 | Payload byte length, 1..255 |
| 21 | declared length | Opaque job payload |
| end | 0 | EOF; no trailing input |

Maximum valid request size is 276 bytes. Tenant identity is **not** in the wire
message: the trusted host supplies its independently authenticated/authorized
scope. Keys and payloads preserve NUL and non-UTF-8 bytes. Payloads are opaque
jobs, not validated email addresses, JSON, MIME, SQL, or executable commands.
Treating them as those formats requires a separate application validator.

`examples/modules/queue-worker/Worker/Request.fib` checks the magic, key length,
length octet, exact nonempty body size, upper bound and absence of trailing body
bytes. A short or excess body fails instead of becoming a different job. It reads
at most 256 body bytes so that the first invalid boundary is detectable. Existing
binary admission/evaluation limits still apply. The source is independently
checked under the same typing/usage rules as other binary programs.

## Validation output is not an acknowledgement

The Fibril program emits `FV01` plus the exact key/length/body only after complete
validation, then flushes. **FV01 means validated, never queued.** The host consumes
this through private callbacks into a 276-byte buffer. Nothing is sent to the
client during validation.

`fibril_worker_enqueue` in `runtime/native/fibril_worker.{h,c}` then:

1. Requires a complete successful validator run and complete input consumption.
2. Verifies the output marker, bounds, declared length and unchanged request
   content. Partial, excessive or mismatched output fails closed.
3. Restores `FQ01` in the private copy and calls the SQLite enqueue API with the
   trusted tenant, 16-byte key and **complete canonical request envelope**. The
   format version is retained for future replay/migration decisions.
4. Returns `FW_OK` with row ID/created flag only after SQLite COMMIT. An identical
   retry returns the same committed ID with created=0.

Every failure returns id=0 and created=0. A conflicting payload under the same
scope/key returns `FW_CONFLICT`; database contention returns `FW_BUSY`; storage
failure returns `FW_STORAGE`. Invalid host arguments are distinct from rejected
untrusted requests. The library has no client IO, process stdio, automatic retry,
network listener or dispatch loop.

Explicit `primRejectBytes` now has structured binary status `F_BINARY_REJECTED`,
distinct from evaluator/budget/adapter failures. The worker maps it to
`FW_REJECTED`; other validator failures are `FW_INTERNAL`. Neither layer parses
diagnostic message strings to make that decision. This is an intentional
extension of the experimental embedding API; legacy CLI diagnostics are unchanged.

The worker must be linked with the generated checked **queue-worker validator**,
not an unrelated binary application. Source/compiler/runtime/host adapters are
trusted according to their documented boundaries; there is no verified ABI or
semantics-preservation theorem. Defensive host checks do not prove an arbitrary
replacement validator correct.

## Build and run the local demonstration

Requires the normal pinned toolchain, C11 compiler and SQLite development library:

```sh
make worker-demo
work="$(mktemp -d)"
python3 -c 'import sys; body=b"example job"; sys.stdout.buffer.write(b"FQ01" + bytes(range(16)) + bytes([len(body)]) + body)' > "$work/request.bin"
./build/worker/queue-worker "$work/queue.db" tenant-a < "$work/request.bin"
# {"status":"queued","id":1,"created":true}
./build/worker/queue-worker "$work/queue.db" tenant-a < "$work/request.bin"
# {"status":"queued","id":1,"created":false}
```

This queue is in a temporary directory for demonstration; retain/backup real
storage deliberately. The host executable is `examples/native/queue_worker.c`.
Its command-line tenant is a **trusted operator input**, not authentication. Do
not expose this executable as a public endpoint that lets clients choose tenants.
The CLI uses stdin EOF to delimit one complete request. A network adapter must
instead enforce transport framing, limits, authentication, deadlines and complete
receipt before invoking the synchronous worker API. A disconnect is not a safe
substitute for an authenticated message boundary.

The demo prints queued JSON only on FW_OK, after commit, with no payload/key/tenant
logging. A failure produces stderr and a nonzero exit, never queued stdout. If
printing/flushing the acknowledgement fails, the row remains committed: retry
the same key/payload, do not generate a new key. The SQLite store is enqueue-only;
queued does not imply remote relay acceptance, delivery, or an exactly-once SMTP
submission guarantee.

## Validation

```sh
make worker-test
make worker-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

Ten integration tests compile the actual checked validator, worker boundary,
SQLite store and local host demo. They cover:

- Binary payloads, maximum 255-byte body, duplicate identity, conflicts and tenant
  separation; stored readback equals the complete canonical envelope.
- Every truncated prefix of a valid request, bad magic/version, zero/mismatched
  lengths, trailing body, and source/host upper bounds: no rows or acknowledgements.
- A valid validation result followed by SQLite BUSY: no success metadata or row,
  followed by successful explicit retry once the lock is released.
- Process exit after commit before application acknowledgement, followed by a
  replay returning the same row without creating another.
- Nine deliberately broken native validator stubs (not typing evidence): empty,
  partial-success-then-error, explicit rejection, overflow, unconsumed input,
  wrong marker, changed key/length and transport failure; none may enqueue.
- Hosted/native validator agreement on representative valid and invalid packets.
- The local demo's first/repeated acknowledgement and empty stdout on failures.

Normal and ASan/UBSan runs pass locally. A dedicated integration step is added to
clean-build CI; the ordinary compiler remains independent of SQLite linkage.
See [durable store limits](durable-queue.md) for what crash tests do not establish,
including untested power loss and ambiguous physical COMMIT failures.

## Remaining production gates

The implementation now joins validation to durable acceptance, but a deployed
service still needs authentication/authorization, admission quotas, secrets,
application-specific payload validation, server framing/timeouts, a queue-state
and lease/fencing model, shutdown/cancellation and observability. SMTP/TLS must
use maintained adapters and explicitly represent uncertain remote submission.
Do not add dispatch to this append-only store without specifying those semantics.
