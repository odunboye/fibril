# Explicit UTF-8 conversion

Status: checked pure source/core operations with native lowering. This does not
expose binary streams or implement a Fibril LSP server. [Pure bytes](bytes.md) and
[text console IO](console-runner.md) retain separate contracts.

## API

- `UTF8Result A : Type` is a small structural failure/success result.
- `primUTF8Encode : (1 text : String) -> UTF8Result Bytes`.
- `primUTF8Decode : (1 bytes : Bytes) -> UTF8Result String`.
- `primUTF8Case Payload Result value failure success` consumes the result once.
  `Payload`/`Result` are erased small types; failure/success branches are
  unrestricted, and success consumes one linear payload. Branches cannot capture
  linear ambient resources through unrestricted application.

Malformed data returns failure, not a replacement string. Empty data succeeds.
NUL, BOM, noncharacters and actual U+FFFD are valid scalar data and are preserved;
there is no normalization, newline processing or BOM stripping. Overlong forms,
UTF-8 surrogates, bad continuations, truncation and values beyond U+10FFFF fail.
The encoder rejects invalid trusted host characters where the backend can
represent them. This is not a refined/nominal result type or a preservation proof.

`examples/core/utf8-bytes.fib` handles both conversion outcomes:

```fibril
decodeAndPrint : (1 bytes : Bytes) -> IO Unit
decodeAndPrint = \(1 bytes : Bytes) => primUTF8Case String (IO Unit) (primUTF8Decode bytes) (putStrLn "invalid UTF-8") (\(1 text : String) => putStrLn text)

main : IO Unit
main = primUTF8Case Bytes (IO Unit) (primUTF8Encode "λ 🌍") (putStrLn "invalid scalar text") decodeAndPrint
```

```sh
./build/exec/fibril run examples/core/utf8-bytes.fib
./build/exec/fibril emit-c-interactive examples/core/utf8-bytes.fib > /tmp/utf8.c
cc -std=c11 -I runtime/native /tmp/utf8.c runtime/native/fibril_runtime.c -o /tmp/utf8
/tmp/utf8
# λ 🌍
```

## Boundaries

Conversion may create a String containing NUL. **Console output still rejects
it**; this API is not a workaround for binary output. Source file control policy
also remains separate. Malformed conversion is a represented pure result, not a
physical IO error or poisoned binary session.

`UTF8Encode`/`UTF8Decode` participate in typing, usage, full/head reduction,
renaming/substitution proofs, thinning, inference, payload/node budgets and file-
reference admission. Guarded candidate conversion reserves worst-case four-byte
encoding expansion before contraction; this conservative guard can reject an
otherwise valid candidate rather than allocate past its policy. Raw reducers and
host APIs do not thereby gain general memory/time bounds or exception safety.

Native Strings already carry explicit UTF-8 bytes. Conversion validates and
shares immutable run-owned/static storage with a different value tag; no payload
passes through a C string. Empty null byte storage is mapped to addressable empty
String storage for existing consumers. Validation reserves one evaluator step
per input byte (including malformed inputs, no refund). Budget/allocation errors
remain runtime failures, distinct from malformed-UTF-8 results. These are not
binary transport requests or its capacity quota.

## Evidence

`test/src/Tests/UTF8Bytes.idr` adds 17 deterministic checks over scalar boundary
vectors, NUL/empty/U+FFFD, malformed sequences, typing, scope transport, resource
scans, admission and source linearity. Full/head reduction agree on the vectors.

`tools/test_bytes_native.py` compares native validation to Python's independent
strict decoder over every one- and two-byte input, selected three/four-byte
boundaries and deterministic random vectors. It checks encode/decode byte
identity for each successful native result. Actual `.fib` cases compare hosted
and compiled execution in both modes: Unicode, empty text, U+FFFD, truncated data
and converted NUL rejected at the console boundary. Raw ABI tests additionally
cover malformed trusted Strings, empty null storage, wrong types, callbacks,
allocation and work exhaustion. Raw fixtures are not evidence of source typing.

```sh
make -j8 bytes-native-test
make -j8 bytes-native-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

Validation passed the unit/property phase, 163 CLI, 19 native-emitter, 7 pure-byte/
UTF-8 native, 9 interactive CLI, 7 editor and 16 handbook tests. All focused IO
subtargets passed in split runs, including 306 hosted checks and 29 resource
differentials. Native byte/codec/console/resource/binary suites passed ASan/UBSan.
The hosted fixture used the documented explicit 450-second deadline on this
machine; no default runner budget or text policy was increased.

Native backend coverage is still an experimental subset; no binary source IO,
compiler-service bridge, scheduler, cancellation or general exception safety is
added by conversion.
