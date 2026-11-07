# Numeric probes and 4 KiB framing

The canonical Fibril-written frame library now accepts **0..4096-byte bodies**.
This was achieved in `.fib` code, without a new arithmetic primitive, a C/Python
header parser or larger runner budgets. General Nat arithmetic remains costly.

## What was measured

`tools/bench_binary_numbers.py` generates named Fibril modules, runs them with
`run-binary`, emits checked C, and runs the compiled program. These are **unframed
numeric probes**, not substitutes for testing the real framing library. Payloads
must be echoed byte-for-byte with empty program diagnostics to count as success.
Checked variants also verify `primBytesLengthIs` before output.

The default matrix uses 99/256/512/1024/4096 bytes and four count constructions:

| Construction | Through 1024 | At 4096 hosted | At 4096 native | Native steps at 4096, checked |
| --- | --- | --- | --- | --- |
| Decimal Nat folds (`10 * value + digit`) | passes | reduction limit | step limit | 100000, rejected |
| Reversed decimal Nat fold | passes | reduction limit | step limit | 100000, rejected |
| Length of a constant byte buffer | passes | passes | passes | 16550 |
| Force-shared byte decimal accumulator | passes | passes | passes | 13402 |

Both checked/unchecked variants were run. Of 80 backend executions, 72 were
successful transfers and 8 were represented budget rejections. Rejections are
**not** counted as equivalence successes. Native instrumentation confirmed the
Nat-fold failures reached the existing 100000-step limit, rather than the
512-depth limit. These are local observations, not portable timings or total
resource bounds. A previous invalid generated-module attempt was corrected
before collecting this matrix; parse failures are not valid limit evidence.

```sh
make -j8 binary-number-test
make -j8 binary-number-bench
python3 tools/bench_binary_numbers.py --sizes 1024,4096 --methods decimal,byte-decimal
```

The tool prints JSON lines, with distinct outcomes for valid transfers, bounded
rejections, other errors, wrong output, signals and deadlines. Unexpected results
produce nonzero exit status. Inputs are capped at eight sizes in 1..4096, four
methods and per-process deadlines of 1..120 seconds. Native observations include
private evaluator-step and arena-payload counters; arena payload is **not** total
live heap or session/stdio storage. The observer uses the actual binary runner
body and does not alter its limits. Times include startup; no speed assertion is
made. `CC` is honored. Temporary artifacts are isolated and removed on exit.

## Source-level strategy

The framer accumulates a number as an immutable byte-buffer length:

1. A digit 0..9 becomes a small zero-filled byte buffer.
2. `tenBytes` constructs ten copies with doubling/append operations.
3. Appending the next digit's buffer computes the next decimal value.
4. `primBytesShare` gives each intermediate a reusable box. Hosted case reduction
   materializes the byte value; native shared thunks memoize it on first demand.
   Reuse avoids repeatedly reducing an unevaluated arithmetic tree.
5. `primBytesLength` supplies Nat only at the IO boundary. Bulk read and exact-
   length checking then use the existing operations.

This is bounded **O(N) representation storage**, not a compact integer or a
solution to arbitrary numeric computation. Four header digits are permitted.
Leading-zero rejection remains strict. For four digits, the source checks the
lexical 4096 boundary **before** constructing the last accumulator; intermediate
buffers are at most 999 bytes and accepted final buffers at most 4096. A fifth
digit is rejected. No oversized body request or oversized decimal buffer is
needed to reject 4097..9999.

## Real framing evidence

`tools/test_framing.py` independently compiles and runs the actual Frame module.
Its 14 methods cover all 0..99 lengths, selected larger boundaries, every length
4000..4096, malformed/oversize headers, binary/Unicode payloads, truncation,
fragmentation and live peers. Two maximum frames succeed in one borrowed session.

A 4096-byte frame consumes **10 requests and 8240 reserved capacity bytes**.
Short input still reserves 4096 for the body; no frame output is produced.
The 4097 boundary is rejected after 5 requests/20 capacity bytes, before reading
the remaining header/body. Open-stdin tests require oversized input to terminate
without waiting for body bytes or EOF. The existing 99-byte 8-request/242-capacity
case remains covered. These tests do not exhaust all possible larger lengths or
headers, prove semantic preservation, or add cancellation/scheduling safety.

The wire grammar is still canonical and strict: no optional Content-Type,
case-insensitive fields, JSON or server lifecycle. See [framing](binary-framing.md)
for the complete contract.

## Validation

The unit/property phase, 163 CLI, 19 native-emitter, 7 byte/codec native, 13
binary-source, 14 raw bridge scenarios, 9 scalability, 6 probe, 14 framing, 9
interactive CLI, 7 editor and 16 handbook tests passed. Framing passed ASan/UBSan,
including two 4096-byte frames and open-input boundary rejection. The complete
40-pair numeric matrix also ran with native ASan/UBSan: each backend returned 36
valid transfers and 4 represented rejections, with no unexpected outcomes.
No core/runtime code, shared package installation or runner budget was changed.
