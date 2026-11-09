# JavaScript backend

Status: experimental checked output-only ES modules. The compiler emits a bundled
runtime and checked program data; generated modules have no npm dependencies.
Node.js 18 or newer is required for the Node launcher and regression tests.

```sh
make build
./build/exec/fibril emit-js examples/core/javascript.fib > program.mjs
node program.mjs
# wrap=0
# λ 🌍
```

`emit-js --source-dir ROOT ENTRY` checks imports, and `emit-js --package MANIFEST`
checks an application package. With no arguments, `emit-js` uses `fibril.yaml`.
Emission writes source only to stdout; it does not run the emitted program.
Diagnostics go to stderr and emission failure produces no JavaScript.

The [example](../examples/core/javascript.fib) also runs with ordinary `fibril run`.
The existing indexed-vector, mutual-data and nested-tree examples can be emitted
with their source directories too.

## Checked fragment

The entry must independently check as `IO Unit`, including type, quantity and
termination admission. The backend supports lazy functions and applications,
checked recursion, Nat and fixed-sequence cases/folds, pairs, boxes, variants,
nominal values and general/indexed/mutual data, strings, pure Bytes operations,
explicit UTF-8 conversions, Words, `pure`, `bind` and `putStrLn`.

General data constructors/cases use the same representation lowering as C.
Erased binders receive no runtime argument. Other arguments and constructor fields
are delayed and memoized; unused arguments and unselected branches are not forced.
Shared globals are emitted once, retaining reference-based code size.

Words use JavaScript `BigInt`, with arithmetic masked to 64 bits. They never pass
through `Number`. Division/remainder by zero return the ordinary tagged result;
they do not throw a JavaScript division exception. `primWordToString` produces
exact decimal text, including values above JavaScript's integer precision limit.
UTF-8 decoding is fatal on malformed encodings and preserves BOM code points;
conversion failure uses Fibril's result variants.

File/input operations, binary transport/iteration, runtime file references and
regions are unsupported. Admission examines the complete original reachable graph,
including types, erased arguments, global signatures/bodies and dead branches.
Unsupported operations are rejected before emission even if evaluation would
skip them. This backend does not implement JavaScript FFI or DOM bindings.

## Embedding

Importing the generated module does not run the program. Call its synchronous
`run` export with an explicit host:

```javascript
import { run } from './program.mjs';
const chunks = [];
run({
  write(bytes) { chunks.push(bytes); }, // Uint8Array containing a complete UTF-8 line
  flush() { /* commit or flush the host sink */ }
});
```

The host must provide both callbacks. Returning `false` or throwing reports a
host error. Promise-returning callbacks are rejected; this API is synchronous.
The callback table is captured per invocation. Repeated/reentrant invocations use
fresh evaluator state. Hosts must treat the generated code and callback functions
as trusted code; the runtime is not a JavaScript sandbox.

All output is staged and validated, including the ban on console NUL characters,
before any callback runs. Evaluation/validation failure invokes neither callback.
Host write/flush failures can leave a visible output prefix and cannot be rolled
back. Successful execution flushes once, including for an empty output plan.
The Node launcher uses synchronous stdout writes and reports errors to stderr.
A symlink or a path containing spaces/Unicode can launch the module directly.

The module can also be imported by an ES-module host with `BigInt`, `TextEncoder`,
`TextDecoder` and top-level-await support. Node-specific imports are guarded by
Node launch detection. Browser/DOM integration and cross-browser testing are
outside this first backend; portable host-mode regression tests run in Node.

## Bounds and verification

Compiler admission permits at most 8192 original reachable core nodes and 8192
literal characters/octet payload units; lowering has a separate depth bound of
1024. Default runtime limits per invocation are:

| Option | Default maximum |
| --- | ---: |
| `steps` | 100000 metered evaluator/work steps |
| `depth` | 256 interpreter entries |
| `bytes` | 16777216 logical allocation bytes |
| `actions` | 64 output lines |

`run(host, {steps: 1000})` may lower these bounds. Unknown options, negative or
non-integer bounds, and attempts to raise a default are rejected. Exhaustion is
an error before output callbacks. Bounds count interpreter work and logical
allocation charges; they do not guarantee wall time, physical JavaScript heap,
garbage collection latency or hard real-time behavior. Host callbacks have their
own resource and failure behavior.

`make javascript-test` compares emitted JavaScript with hosted and native C output
for checked programs, including Words, bytes, UTF-8, erased arguments, constructors,
recursion and the standard-library conformance application. Trusted-IR runtime
fixtures separately check memoization, cycles, invalid encodings, budget exhaustion,
callback failures and reentrancy; those fixtures do not establish source admission.
The suite is included in `make test`, and CI installs Node. The runtime is bundled
by `tools/embed_javascript_runtime.py`; `make javascript-runtime-check` rejects a
stale bundle. Regenerate it with `make javascript-runtime` after runtime edits.
