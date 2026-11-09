# TCP networking

Status: experimental POSIX TCP profile for checked Fibril programs. The
[Net.TCP](../stdlib/net/src/Net/TCP.fib) and
[Net.Stream](../stdlib/net/src/Net/Stream.fib) libraries are Fibril source. The
[platform boundary](../runtime/native/fibril_network.c) performs socket syscalls;
no libpq, database client, HTTP implementation or general source FFI is involved.

## Build and run

```sh
make network-demo
./build/network/echo
```

The [example](../examples/modules/tcp-echo/src/Main.fib) announces its ephemeral
IPv4 loopback port, accepts one connection, echoes one available chunk, closes
both sockets and prints its sent-byte count. This is a transport demonstration,
not an HTTP server or a whole-message echo protocol. For a real application, use
explicit framing and loop over bounded operations.

The equivalent emission/link steps are:

```sh
./build/exec/fibril emit-c --package examples/modules/tcp-echo/fibril.yaml > echo.c
cc -std=c11 -O2 -Wall -Wextra -Werror -I runtime/native echo.c -o echo
```

`emit-c` selects the network entry when the program uses sockets. That generated
file includes `fibril_runtime.c`, `fibril_network.c` and
`fibril_network_runtime.c` itself (one translation unit, because the TCP code
uses the runtime's statics), so there is no runtime file to link and no TCP code
in any other build. It states its build command in a comment at the top. Hosted POSIX
only (`FIBRIL_NO_HEAP` is rejected). A program that uses sockets cannot also use
console input, files or binary stdio; `emit-c` rejects that combination.
`emit-c-network` remains as an alias that always selects the network entry. With no arguments, emission
uses `fibril.yaml`. The entry independently checks as `IO Unit`; checking and
emission perform no network activity. Emission produces C, not an executable.

Library dependency:

```yaml
dependencies:
  net:
    path: ../fibril/stdlib/net
```

Use a valid relative local dependency path for your manifest, then `import Net.TCP` and,
for bounded exact reads, `import Net.Stream`.

## Operations and ownership

| Function | Result inside IO |
| --- | --- |
| `connect address port timeout` | `NetResult Socket` |
| `listen address port backlog` | `NetResult Listener` |
| `accept listener timeout` | `SocketAccept`: listener and `NetResult Socket` |
| `read socket capacity timeout` | `SocketRead`: socket and `NetReadResult` |
| `writeAll socket bytes timeout` | `SocketWrite`: socket and `NetResult Word` |
| `localPort listener` | `ListenerPort`: listener and `NetResult Word` |
| `shutdownWrite socket` | `SocketShutdown`: socket and `NetResult Unit` |
| `close socket` / `closeListener listener` | `NetResult Unit`, handle consumed |

`Socket` and `Listener` are different opaque types. Source has no constructors
for them and cannot substitute a Word/file descriptor. Operations consume linear
ownership and return its successor, including represented read/write/accept
failures. A stale token or wrong-kind reference also fails defensively at runtime.
There is no implicit socket copying or explicit source-level raw-pointer escape.

Use ordinary two-field `case` expressions to unpack ownership-returning results,
then `resultCase` or `readCase`. These helpers take unrestricted branch callbacks:
pass an ambient socket *after* choosing a callback rather than capturing a linear
socket inside an unrestricted callback. The echo example demonstrates this.

`NetReadResult` distinguishes EOF, a nonempty byte chunk, and an error. Reads may
return fewer bytes than requested; TCP has no message boundaries. Binary payloads
preserve NUL and arbitrary octets. `writeAll` sends the full payload on success;
its successful Word is the byte count. Empty writes succeed without a send.

`NetError` contains two linear Words: status category and transferred prefix.
`primNetWordToString` consumes a linear Word for diagnostic rendering.

| Category | Meaning |
| --- | --- |
| 2 | Timeout |
| 3 | Invalid address, port, capacity, timeout or other argument |
| 4 | OS/socket failure |
| 5 | Session socket capacity or generation limit |

The low-level trusted C API additionally preserves `errno`; source errors
currently expose the portable category and prefix only. Connect failure has no
handle. After close, ownership is consumed even if close reports an error. Writes
are not transactional: the transferred prefix can already be visible to the
peer, and a successful send does not establish peer application receipt. Retrying
an entire failed message can duplicate its accepted prefix.

## Deadlines, storage and cleanup

- Addresses must be numeric IPv4 or IPv6; no DNS or IPv6 zone identifiers yet.
  IPv6 listeners use `IPV6_V6ONLY`; they do not also accept IPv4.
- Connect ports are 1–65535; listen permits zero for an ephemeral port. Backlog
  is 1–4096, subject to OS limits.
- Timeouts are Words in milliseconds, 0–3,600,000. Zero polls readiness without
  waiting. Nonblocking syscalls and `poll` use one monotonic deadline per
  operation, including retries/partial writes. Deadlines are not real-time
  scheduling guarantees. Listen/close/shutdown/local-port operations do not wait
  for network readiness.
- Read capacities are 1–1 MiB; writes are 0–1 MiB. Each runner invocation has at
  most 64 simultaneously live sockets, 4096 executed socket/console operations,
  and 4096 pending IO continuations. Existing evaluator limits (100000 steps,
  depth 512, 16 MiB allocation) and emitter limits (8192 core nodes/literal
  admission) still apply.
- Allocations are retained until runner exit. Reads reserve their capacity before
  receiving, even if they time out. Large/repeated reads can exhaust the arena.
- The runner owns the session and attempts to close every remaining socket on
  success or failure, before freeing evaluator memory. Explicit close reports
  errors. Cleanup errors fail the run; close is never retried after EINTR because
  descriptor ownership after interruption differs between operating systems.
- Descriptors are nonblocking and close-on-exec. Sends suppress SIGPIPE per
  socket/call; the library does not change process-global signal handlers.

`readExactly fuel socket count timeout` returns `ExactRead`, containing the
socket and one of `Complete bytes`, `Ended prefix`, `Failed prefix error`, or
`Exhausted prefix`. It performs at most `fuel` reads and requests at most 64 KiB
per read, without consuming beyond the requested count. Count zero needs no read.
Counts above 256 KiB are refused: the result is `Exhausted` with an empty prefix and
nothing is read (a count of exactly 256 KiB reads normally).
Its timeout applies **per read**, not to the whole helper. Prefix assembly copies
bytes and is intended for bounded messages; it is not a zero-copy buffer builder.
All copies count against the invocation's allocation/evaluation limits.

## Runner separation and current limits

`emit-c` selects the network profile when the program reaches network syntax
(including erased/dead syntax). The interactive, resource, binary, JavaScript and
embedded emitters/runners reject reachable network syntax. The network profile permits console output for
logging but rejects console input, file resources and borrowed binary stdio,
including erased/dead syntax. Effects execute incrementally; earlier output and
network writes are not rolled back after a later error.

The initial platform supports POSIX macOS/Linux APIs. It waits synchronously for
one operation at a time; nonblocking descriptors do not make this an asynchronous
scheduler. There is no DNS, TLS, UDP, Unix-domain sockets, Windows adapter,
cancellation token, connection pool or multi-connection readiness API yet. Neither
HTTP nor a PostgreSQL client is implemented by this library. Native code, the OS,
and compiler/runtime remain trusted; these tests are not a network safety proof.

`make network-test` runs real loopback, fragmented exact-read, EOF/timeout/fuel,
wrong-runner, ownership and defensive-runtime tests, including ASan/UBSan. The
suite is also part of `make test`. No external network access is required.
