# Optional single-node durable enqueue store

Status: experimental trusted POSIX/SQLite adapter, implemented and tested outside
the Fibril checker. This is **enqueue-only storage**, not a mail service, a checked
source primitive, a dispatcher, or a proof of durable/linear resource semantics.
A [checked enqueue integration](enqueue-worker.md) now connects a bounded job
validator to this store through a trusted host. It is not exposed as a Fibril
source primitive or a Content-Length frame server.

The first production-runtime slices now supply console and binary embedding.
This slice supplies a separately linked persistence boundary, so a future worker
can persist an accepted application request before acknowledging it. The integration defines a versioned opaque-job envelope; authentication,
authorization and email-specific payload validation remain follow-up work. The
existing checked request-label/email examples are still pure models.

## Scope and dependency

`runtime/native/fibril_queue.{h,c}` implements an opaque queue handle using SQLite
3.35 or later. It is optional: the compiler, console runtime and binary runtime
do not link SQLite by default. Compile/link the adapter with SQLite explicitly:

```sh
cc -std=c11 -I runtime/native host.c runtime/native/fibril_queue.c \
  $(pkg-config --cflags --libs sqlite3) -o host
```

Development packages are typically `libsqlite3-dev` on Debian/Ubuntu, or the
platform SQLite SDK/Homebrew SQLite on macOS. The test driver uses pkg-config
when present, otherwise `-lsqlite3`. `SQLITE_CFLAGS` and `SQLITE_LIBS` can override
that selection. This is a local-filesystem, **single-node** profile, not a
multi-node lease/queue design. SQLite, its VFS, the C library and OS/storage stack
are trusted components. No custom cryptography, SQL parser or database is added.

## Request and idempotency contract

The trusted host supplies an `FQueueRequest`:

| Field | Representation and bound |
| --- | --- |
| tenant | 1..128 opaque bytes; authenticated/authorized by the host |
| key | 1..128 opaque bytes; idempotency key scoped to that tenant |
| payload | 1..65536 opaque bytes; exact canonical request representation |

These are structural bounds, **not** email-address, MIME, JSON, authentication or
application-schema validation. Empty values, missing pointers and over-limit
lengths are rejected before beginning a transaction. All SQL is fixed and uses
bound BLOB parameters. Embedded NUL, quote bytes and invalid UTF-8 are preserved;
identities are not implicitly decoded, normalized or truncated as C strings.

`fibril_queue_enqueue` uses `BEGIN IMMEDIATE` to serialize writer decisions:

1. Look up the tenant/key inside the transaction.
2. If present with identical payload, return its existing ID with `created=0`.
3. If present with different payload, roll back and return `FQ_CONFLICT`.
4. Otherwise insert one row and commit; only then return its ID with `created=1`.

Failure resets ID/created to zero. The API does not claim acceptance on an SQLite
error. Different tenants may use the same key; different binary keys remain
independent even if their prefixes before NUL match. SQLite row IDs are local
implementation identifiers, not unguessable public IDs or authorization tokens.

The host must serialize an application's semantically equivalent requests
canonically **before** selecting the payload. Byte equality is not a claim of
JSON equivalence or an email delivery identity. Changing encoding under the same
key can legitimately produce a conflict. There is no retention/deletion API yet;
keys are retained indefinitely and may not silently be reused for new requests.

## Durability and crash behavior

Opening requires WAL mode and sets `synchronous=FULL` on the adapter connection.
Success is returned after SQLite COMMIT, not merely after a write to an output
buffer. Mandatory durability relies on SQLite/VFS/OS/device honoring sync; this
is not a power-loss test or an independently verified storage guarantee.

A process may die **after commit but before an application acknowledgement**.
The same tenant/key/payload retry returns the existing row. An uncommitted
transaction is not accepted and is recovered by SQLite on reopen. A COMMIT IO
error may itself have an uncertain outcome; return a storage error and reconcile
or retry the **same** idempotent request. Inventing a new key can create a duplicate.

SQLite BUSY/LOCKED is returned explicitly as `FQ_BUSY`, with no library sleep or
retry policy. A host can apply bounded backoff/cancellation without duplicating
accepted rows. Enqueue idempotency does **not** provide exactly-once SMTP delivery.
Once a remote submission is uncertain, a separate worker state/reconciliation
policy is required; no SMTP dispatch or retry is implemented in this slice.

## Readback, errors and lifecycle

`fibril_queue_get` looks up the tenant/key and copies the committed payload into
caller-owned storage. No SQLite pointer escapes. On `FQ_BUFFER_SMALL`, it reports
the required length and row ID without copying; capacity zero/NULL can be used as
a size query. Other failures reset ID/length. `FQ_NOT_FOUND` is distinct from
storage failure; corrupt databases must not look like empty queues.

`FQueueResult` reports `FQ_OK`, `FQ_INVALID`, `FQ_CONFLICT`, `FQ_NOT_FOUND`,
`FQ_BUFFER_SMALL`, `FQ_BUSY`, `FQ_STORAGE`, or `FQ_UNSUPPORTED`. Extended SQLite
codes accompany SQLite failures, but raw SQL error text/payloads are never logged.
There is no process stdio, process termination, automatic retry or background
thread in the adapter. The caller decides how to report and redact errors.

A handle is sequential and must not be shared concurrently or used after fork.
Independent processes/handles use SQLite locking. Every prepared statement is
finalized; close releases the connection. Host buffers are borrowed only for the
synchronous operation. Use trusted native callers: this C API does not validate
arbitrary pointers, preserve Fibril typing by itself, or constitute a sandbox.

## File and schema policy

Use a stable trusted local directory owned by the service, preferably mode 0700.
The adapter creates database files with mode 0600 without changing process umask.
It rejects symlinks, hardlinked/nonregular files, foreign-owned files, and files
with group/world access. URI and in-memory opens are rejected. SQLite manages its
own WAL/SHM files. Deployment backup/retention must use SQLite-aware procedures;
copying only the main file while WAL is active is not a complete backup.

The pre-open descriptor is checked and closed before SQLite opens the path.
A malicious actor able to replace that path or sidecars can race the later open;
this is **not** a directory-fd sandbox or protection against hostile local file
mutation. Do not point it at an attacker-controlled directory or database.
File permissions are not encryption at rest or multi-tenant authorization.

Schema version 1 is owned by this adapter. Unknown versions, unrelated nonempty
databases, counterfeit table definitions and additional user schema objects
(including triggers) are rejected, not migrated or repaired. Initial inspection
occurs before changing journal mode and is repeated under the initialization
write lock. Schema initialization is transactional. Schema checks reduce
accidental misuse; they do not turn an adversarial database file into trusted data.

No queue quota, expiry, compaction, schema migration, dispatch lease, fencing,
acknowledgement state, metrics, database encryption, or disk-space policy is yet
provided. Those are explicit production gates, not implied by durable enqueue.

## Validation

```sh
make queue-test
make queue-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

Twelve integration tests compile a C harness against the public adapter API and
exercise binary bounds/identity, conflict preservation, tenant scope, reopen and
readback, undersized buffers, maximum payload, lock contention, and 12 competing
processes retrying the same request (one committed row/one creator). The bounded
retry in that contention fixture is a **test-host** policy, not library behavior.

Crash fixtures abandon a raw SQLite transaction without close/rollback, and exit
after an adapter COMMIT without close/application acknowledgement. Reopen checks
absence/presence and safe duplicate retry respectively. These exercise process
exit and SQLite recovery, not arbitrary power loss, disk-full COMMIT, torn writes,
or every instruction in the adapter. Permission/symlink/hardlink, corrupt-file,
foreign-schema, counterfeit-schema, extra-trigger and unknown-version cases are
also covered. The local normal and ASan/UBSan runs pass. A separate lightweight
CI job is configured to run both on Ubuntu; SQLite is not made a dependency of
the ordinary compiler/test build.

## Next integration gate

The [enqueue worker](enqueue-worker.md) now validates a versioned request in
checked Fibril, buffers the validation result privately, stores the full canonical
envelope and acknowledges only after COMMIT. Before deployment, add authenticated
tenant selection, application-specific job validation, quotas, a dispatch state
and lease/fencing model, and the uncertain remote-submission contract. The local
host demonstration is not an authenticated worker service.
