# Checked native resource emission

Status: explicit checked-core emission and hosted/native differential tests.
Source file primitives and resource CLI commands remain disabled.

`Driver.Native.Emit.emitCheckedResourceC requests lineLimit term` checks a closed
`IO Unit` entry and selects `fibril_native_resource_run`. It lowers scoped input,
ownership-returning reads, pair construction and pair elimination, in addition
to the existing console subset. Output-only `emitCheckedC` and console-only
`emitCheckedInteractiveC` retain their fail-closed resource gates.

Admission rejects caller-supplied runtime file references anywhere in the
original syntax, including erased arguments and annotations. Checking precedes
lowering. Pair annotations must expose Sigma within the reduction budget;
code generation derives both erasure flags from its quantities rather than
assuming both fields survive. Erased lambda arguments still occupy environment
slots, preserving de Bruijn indices. Region arguments carry no runtime authority;
the resource registry introduces actual handle identities and generations.

Emission and checking perform no file IO. Generated C links against
`runtime/native/fibril_runtime.c` in the same way as other checked emission.
The supported computational subset is still experimental, not all checked core.
The resource entry grants read access to supplied paths, not a filesystem sandbox
or a complete source capability system.

## Text boundary

Hosted reads now collect bytes through `fgetc`, with at most four bytes per
allowed scalar plus CR/LF retained. Overflowing lines are drained through LF/EOF.
Strict UTF-8 decoding uses the existing scalar decoder. Native reads enforce the
same text rules: malformed sequences and embedded NUL are represented errors,
not replacement decoding or silently truncated strings. Valid U+FFFD is kept.
Text writes reject NUL before either backend can truncate or emit it. This is
not binary IO. Filename NUL rejection remains a separate acquisition guard.

These changes fix an observed mismatch: the previous hosted `fGetLine` path
silently turned `a NUL b LF` into `a`, while native retained the NUL and suffix.
Reads after a text error or buffer overflow consume the next line with successor
ownership. Captured byte bounds do not bound elapsed time, draining work, total
host allocation or arbitrary host exceptions.

## Evidence

`make -j8 io-resource-emitter-test` compares 29 checked-core cases against a real
compiled hosted executable. Cases include Unicode/CRLF/EOF, text failures,
continued reads after errors and overflow, nested scopes, two successor reads,
both pair erasure positions, four recursive fold families inside live scopes,
acquisition failure, NUL filenames, output failure,
and request exhaustion before acquisition, in a body and after visible output.
Open-error wording is normalized by the fixture; failure categories and process
status are compared without requiring platform-specific diagnostics to match.
The hosted fixture explicitly flushes failure prefixes for comparison with C
process exit; the resource runner promises final flush only on success.

Unlike `idris2 --exec`, the compiled hosted fixture propagates `exitFailure`, so
failure-status comparisons are meaningful. Direct adversarial C runtime tests
separately exercise close counters and injected cleanup failures; these checked
fixtures do not themselves inject OS close failures. Sanitizer coverage is
available with `CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'`.

These are finite observations, not a preservation proof, general exception
safety, world-token IO or permission to expose source file operations yet.
