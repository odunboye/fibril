# Native interactive runtime slice

Status: trusted C runtime, checked interactive C emission and differential tests.
Source-level input is exposed through the explicit standalone interactive
[API and file drivers](io-input.md).

`f_read_line` constructs an inert request. The separate
`fibril_native_interactive_run(entry, requests, line_characters)` executes reads
and writes incrementally; the existing `fibril_native_run` still prepares all
output first and does not execute read requests.

Interactive reads flush stdout before reading. EOF, line and represented errors
use the same positional variant tags as `readResultType`: 0, 1 and 2. Line/error
payloads are String values. Write failures terminate execution; read errors are
values that the program may handle. Final stdout flushing is checked on success.
Earlier output is not rolled back when later computation or request fuel fails.

Request fuel counts writes and reads, not pure returns. It is shared across bind
continuations. Admission allows at most 100,000 requests and 8,192 characters per
line; existing allocation/evaluation/depth budgets also apply. These are not
blocking, elapsed-time or overall work guarantees.

Native input:

- removes one LF or CRLF terminator;
- preserves an unterminated line, including a final bare CR;
- distinguishes empty input lines from EOF and host read errors;
- validates scalar UTF-8 and counts decoded characters;
- returns malformed UTF-8 as an input-error value;
- bounds its per-line byte buffer by four times the character limit plus two;
- consumes through newline/EOF even when a line exceeds buffer capacity, then
  returns a length error. This draining can block without a timeout.

The host adapter instead checks length after host decoding/allocation, and
malformed-input decoding follows Idris/Chez. Only the documented well-formed
UTF-8 subset is a current cross-backend compatibility target. No source/native
input equivalence theorem is claimed.

`tools/test_io_native_runtime.py` now has 17 direct runtime tests, including a
pipe test observing the flushed prompt before supplying input and a real read
error from a directory descriptor. Those fixtures are trusted C, not evidence of source checking or emission.
`Driver.Native.Emit.emitCheckedInteractiveC requests lineLimit term` now checks
a closed `IO Unit` entry and explicitly selects interactive lowering and its
runtime. `emitCheckedC` remains output-only and rejects computational reads.
Interactive admission limits are checked before generating C.

`tools/test_io_interactive.py` resolves `examples/core/read-line.fib` through
both standalone file drivers and checked interactive emission. Seven differential cases cover
Unicode CRLF, EOF, empty/unterminated lines, bare final CR, length errors and a
Unicode length boundary. These are well-formed UTF-8 tests, not malformed-input
parity. Actual interactive CLI dispatch is covered separately by
`tools/test_io_cli.py`. `make io-test` includes this suite and
retains the output-only checked-emission differential examples.
