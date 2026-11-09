# Experimental checked C emission

## Use cases and status

**Implemented first slice:** check a closed `main : IO Unit`, emit C that computes
the program at native runtime, then explicitly compile and run it using a C11
compiler. This is a useful path for console prototypes and testing the native
runtime boundary. It is **not a production backend** or a networked email
service: there is no native HTTP, SMTP, TLS, storage, UI, FFI or general data
support yet. Nat, fixed unary and list-shaped recursive
values, their structural folds and direct cases are supported. A size-change-admitted
`Fix` (general recursion, see [function equations](function-equations.md#general-recursion))
is emitted as a recursive closure and agrees with the hosted evaluator, but it runs
inside the same fixed evaluation budget as everything else (100000 steps, depth 512).
Native emission does not widen how much work a program can do, but a [tail call](#tail-calls)
no longer consumes depth, so only the step budget bounds a tail-recursive loop. Finite
nullary/unary nominal variants and cases are supported, including
[pure pair payloads and record lowering](native-pure-pairs.md). For ordinary
development, the existing bounded reference `fibril run` remains an alternative.

~~~sh
# From projects/fibril; the shell owns the redirection and can truncate main.c.
./build/exec/fibril emit-c examples/core/hello-world.fib > main.c
cc -std=c11 -Wall -Wextra -I runtime/native main.c runtime/native/fibril_runtime.c -o main
./main
~~~

Emission also accepts `--source-dir ROOT ENTRY`, `--package fibril.yaml`, or no
arguments (the current directory's `fibril.yaml`). Package and module visibility
and checking are unchanged. `emit-c` writes C **only to stdout** and diagnostics
to stderr; it does not create files, run a compiler, execute generated code,
run hooks or invoke a shell. The caller controls redirection: redirecting over an
existing file can truncate it even when emission subsequently fails. Do not
redirect over source files. There is no atomic output-file or sandbox guarantee.

![Checked C emission boundary](diagrams/native-c.svg)

## Tail calls

A call in tail position (an application, an `if`, or a branch of a `case`, whose result is the
function's result) runs in the same evaluator depth slot instead of nesting. Each transfer still
costs one step, so step accounting is unchanged and only the depth limit moves: a loop of 2048
tail calls peaks at depth about 20 where it used to exhaust the 512 depth limit. Non-tail recursion,
such as `primWordAdd 1w (count p)`, still nests and still stops at the depth limit.

Laziness is unchanged: arguments are still thunks, an ignored argument is never evaluated, and a
thunk's memoized value is always a completed value. Folds (`natRec` and friends), regions, IO
and thunk forcing are not tail positions. A lazily accumulated argument can still build a chain of
deferred work that is forced later, nesting as deep as the chain is long, so an accumulator should
be forced as it goes if the loop is long (`experiments/fib-lexer` shows one way).

The mechanism is `evaluate` in `runtime/native/fibril_runtime.c`: the ten helpers marked
"tail position" return a sentinel after recording the continuation, only `evaluate` receives it,
and the emitter calls those helpers only as `return helper(...)`. The JavaScript backend loops
inside its single `evaluate` instead (see [javascript](javascript.md#depth-and-tail-calls)).

## Configurable limits

The defaults stay 100000 steps, depth 512 and 16 MiB of allocation. Two ways change them:

- **At build time**, for a standalone program: compile the runtime with
  `-DF_MAX_STEPS='((size_t)N)'`, `-DF_MAX_DEPTH=...` or `-DF_MAX_BYTES=...`.
- **Per invocation**, for an embedder: `fibril_native_embed_limited(entry, host, &limits)` and
  `fibril_native_binary_embed_limited(entry, requests, capacity, host, &limits)` take an
  `FNativeLimits {steps, depth, bytes}`. A zero field keeps the default and `NULL` keeps all of them.
  The existing `fibril_native_embed` and `fibril_native_binary_embed` are unchanged.

Raising a limit is the embedder's decision, so it is allowed, but every limit stays finite: a value
above its ceiling (1073741824 steps, 16384 depth, 1073741824 bytes) is rejected with
`INVALID_ARGUMENT`, never clamped, and nothing runs. The defaults are unchanged, and **lowering** a
limit for a tighter or untrusted workload is always safe.

**The depth ceiling is a hard bound on the setting, not a portable safe stack depth.** Accepting
16384 does not mean 16384 nested evaluations fit on your stack. Depth is a C-stack bound: each unit
is several C frames, so what fits depends on the stack size, the compiler and optimization level,
and the platform. One data point, not a guarantee: on an 8 MB main-thread stack built at `-O1`, about
33000 nested evaluations ran and about 65000 overflowed (roughly 120 bytes per unit). Unoptimized
builds and small thread stacks need much less. Choose a depth for the stack the call actually runs
on, and keep the default 512 unless you have measured that stack. The embedded no-heap profile keeps the default evaluation limits (its
allocation bound is the arena).

Embedders also learn what a run used: `FNativeResult` and `FBinaryResult` carry
`usage {steps, peak_depth, bytes}` on success and on failure, so a limit can be chosen from
evidence. The JavaScript backend is different: its `run(host, options)` limits can be lowered
but not raised (see [javascript](javascript.md)).

## Resource diagnostics

A native run that exhausts its evaluation budget says which limit it was:
`native evaluation budget exhausted (step limit)` or `(depth limit)`; allocation exhaustion
reports `native allocation budget exhausted`. Set `FIBRIL_STATS=1` to make a standalone
program (`run`, interactive, resource, binary and network entries) write one extra line to
**stderr**, `fibril stats: steps=N peak_depth=N bytes=N`, on success and on failure. Stdout
is never touched and nothing is printed unless the variable is set (`0` or empty counts as
unset). `bytes` is total allocation charged against the allocation budget. The embedding APIs
report the same numbers in their results (see [configurable limits](#configurable-limits)).

## What is compiled

The supported computational subset is Unit, Bool and conditionals, String
literals, append and equality, variables, lambdas and application, Unit case,
finite nominal and variant values/cases, pure pairs and pair cases; Nat and the fixed unary and
list-shaped recursive constructors, folds and direct cases; and the inert IO
forms `pure`, `bind`, and `putStrLn`. Source lets and do notation lower to those ordinary core forms.
The closed entry is independently checked against `IO Unit` in its checked
global environment **before** code generation, including erased-global barriers
and runtime quantity analysis. Every module/package declaration must pass
admission; complete reachable signatures/bodies are also scanned for backend
capabilities and counted before emission.

The generated C computes supported core terms at native runtime. Arguments are
lazy memoized thunks; [variable-argument forwarding](native-variable-forwarding.md)
reuses an existing cell for direct variable arguments. Closures keep
a slot for every binder. An erased binder receives an unforceable sentinel, and
forcing it is a runtime error. The runtime uses the checked closure's quantity;
this is an implementation choice backed by tests, **not a proved erasure or
quantitative-preservation theorem**. Type annotations and the IO type fields are
not executed; admitted type-only terms become an internal erased placeholder.
Finite nominal wrappers and variant payloads retain lazy thunks; a case evaluates
only its selected branch, in the case's environment. Recursive constructors
retain lazy field thunks, and a fold's recursive result is a memoized suspended
fold over the actual tail. Ordinary fold tails are erased; `natRecWith` retains
its runtime predecessor. An erased payload remains an application to an erased
binder and is never forced by checked code. Unsupported
computational forms fail emission, including when encountered inside an argument
that would later be erased. Pure pair values and cases, including wider record
payloads, lower in every native mode while retaining that mode's effect gates.
Arbitrary effects are not silently simulated.

Source strings are emitted as generated decimal UTF-8 byte arrays, not pasted
into C literals or identifiers. Supported programs can compute strings, call
functions and build continuations at runtime. `tools/test_native.py` compiles
and executes emitted C and compares successful supported samples with `run`;
this is sampled evidence, not a semantics-preservation proof.
[Unsigned 64-bit Word](words.md) arithmetic, comparison, division, Nat conversion and decimal formatting are supported natively, with
`tools/test_native_words.py` as its differential test.

## Host embedding

Ordinary `emit-c` output also supports a [synchronous host embedding entry](native-embedding.md).
Compile it with `-DFIBRIL_EMBED_ONLY` and call `fibril_program_embed` with explicit
write/flush callbacks to avoid process-global console IO. Structured results,
per-invocation arena cleanup and preflight text validation are implemented; this
is not a general source FFI or a network/storage service runtime. Standalone
execution and other emission modes retain their existing behavior.

## Runtime boundary and limits

`runtime/native/fibril_runtime.{h,c}` and the chosen C compiler are trusted host
components. The runtime constructs a complete list of up to 64 console actions
and checks the final Unit value **before the first write**, similarly to `run`'s
staging. Its evaluation/arena limits differ from the reference planner; success
or exhaustion in one is not guaranteed to match the other. Once writing begins,
a host error can leave partial output; writes are not transactional.

Current prototype policies: at most 8192 shared-graph core nodes and 8192 aggregate
literal/key characters before emission; native execution admits at most 100000
evaluation/planning entries, depth 512, 64 actions, and 16 MiB of requested
arena payload. Allocation bookkeeping, libc overhead, C stack, executable data,
and compiler memory are not included in that payload count. Character count is
not a byte bound, and host String length measurement is not a portable bounded-time
operation. Exhaustion is an error, not a guessed result. The arena is freed on
normal/error exit; there is no per-value ownership optimization.

These controls are admission and failure policies, **not proofs** of memory
safety, bounded memory, hard deadlines, erasure, backend correctness or sandboxing.
The runtime uses C stack and host `malloc`, `fwrite` and `fflush`; platform failure
behavior and compiler/library correctness remain trusted. There is no verified
ABI or promise that output paths, source snapshots or external dependencies are
immutable. Named module globals now use a [checked shared environment](shared-checked-globals.md).
Admission counts the entry and each reachable signature/body once, including
erased and dead syntax. Bootstrap prelude expansion and the existing graph,
construction, conversion and runtime limits still constrain larger programs.

Run the native integration suite with a C11 compiler available as `CC`:

~~~sh
make -j8 native-test
~~~

The suite checks real C compilation and output, finite and recursive constructor/
case behavior, structural folds, laziness and captured environments, erased payloads and globals, unsupported
forms, UTF-8/escaping, imported modules and packages, action limits, and failure
before stdout. It does not validate arbitrary compilers, architectures,
operating systems, native memory safety or production readiness.

The separate [TCP network profile](network.md) provides checked socket operations
and Fibril transport helpers. It uses a different explicit runner; these console
and binary profile guarantees do not automatically extend to network effects.
