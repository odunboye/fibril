# Experimental checked C emission

## Use cases and status

**Implemented first slice:** check a closed `main : IO Unit`, emit C that computes
the program at native runtime, then explicitly compile and run it using a C11
compiler. This is a useful path for console prototypes and testing the native
runtime boundary. It is **not a production backend** or a networked email
service: there is no native HTTP, SMTP, TLS, storage, UI, FFI, general recursive
function (a size-change-admitted `Fix` fails closed) or general data support yet. Nat, fixed unary and list-shaped recursive
values, their structural folds and direct cases are supported. Finite
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

## What is compiled

The supported computational subset is Unit, Bool and conditionals, String
literals, append and equality, variables, lambdas and application, Unit case,
finite nominal and variant values/cases, pure pairs and pair cases; Nat and the fixed unary and
list-shaped recursive constructors, folds and direct cases; and the inert IO
forms `pure`, `bind`, and `putStrLn`. Source lets and do notation lower to those ordinary core forms.
The whole closed expanded entry is independently checked against `IO Unit`
**before** code generation, including the original erased-global barriers and
runtime quantity analysis. Checked module/package dependencies must all pass.

The generated C contains a function for each supported core subterm, not a list
of precomputed output strings. Arguments are lazy memoized thunks; closures keep
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

## Runtime boundary and limits

`runtime/native/fibril_runtime.{h,c}` and the chosen C compiler are trusted host
components. The runtime constructs a complete list of up to 64 console actions
and checks the final Unit value **before the first write**, similarly to `run`'s
staging. Its evaluation/arena limits differ from the reference planner; success
or exhaustion in one is not guaranteed to match the other. Once writing begins,
a host error can leave partial output; writes are not transactional.

Current prototype policies: at most 8192 raw core nodes and 8192 aggregate
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
immutable. Transparent checked globals are still expanded into closed core, so
existing graph and expansion budgets continue to limit larger programs.

Run the native integration suite with a C11 compiler available as `CC`:

~~~sh
make -j8 native-test
~~~

The suite checks real C compilation and output, finite and recursive constructor/
case behavior, structural folds, laziness and captured environments, erased payloads and globals, unsupported
forms, UTF-8/escaping, imported modules and packages, action limits, and failure
before stdout. It does not validate arbitrary compilers, architectures,
operating systems, native memory safety or production readiness.
