# Learning from Zig

Status: recommendations for Fibril, not adopted syntax or implemented platform APIs.

Source: [Zig 0.15.2 language reference](https://ziglang.org/documentation/0.15.2/).
Use this versioned reference, particularly Memory, Error Union Type, defer/errdefer,
comptime, Build Mode, Illegal Behavior, C, Targets, and Zen. Zig remains a systems
language with manual lifetime obligations, not a proof assistant or a fully
memory-safe language.

## Make costs and responsibilities visible

| Zig lesson | Application to Fibril | Boundary |
| --- | --- | --- |
| Explicit allocator parameters by convention | Allow allocator/storage capabilities and caller-provided buffers in allocation-sensitive APIs; support hosted and no-heap libraries without global assumptions | Do not require manual allocation everywhere or replace the current Idris-managed implementation prematurely |
| Allocation failure is a real result | Specify failure paths; later inject allocation failures and test cleanup | Idris-managed OOM is not currently recoverable through Fibril's checker APIs |
| defer and errdefer | Keep acquisition and cleanup close; explore scoped resource combinators compatible with linear use | Syntax alone does not prove cleanup, panic/cancellation behavior, or bounded cost |
| Error unions and propagation | Use explicit typed failures, precise diagnostics, and contextual error traces | Keep failure, inconclusive checking, panic, and logical impossibility distinct |
| Compile-time computation | Reuse checked pure definitions for specialization, table generation, and deriving | Compile-time execution is not proof; dependent normalization is not arbitrary effectful build execution |
| Explicit target/ABI information | Record architecture, features, ABI, endianness, and toolchain in artifacts; make cross-compilation a first-class workflow | Board support and timing evidence are still target-specific |
| C interoperability | Specify layouts, calling conventions, pointer ownership, nullability, alignment, and lifetimes | Imported signatures do not prove foreign implementations satisfy invariants |
| Bounds-aware slices and optional values | Prefer bounded buffer APIs and explicit absence; eventually use dependent bounds where practical | Lifetime/aliasing safety is a separate problem from bounds checking |
| Integrated testing and tested documentation | Keep runnable examples and tests in the normal workflow; later add allocator/FFI failure injection | Tests are evidence, not consistency or correctness proofs |
| Readability and small abstractions | Favor clear names, explicit costs, cohesive modules, predictable behavior | Borrow principles, not every Zig restriction or its syntax |

## A worked design question: a bounded encoder

A future embedded encoder could accept an owned input and a caller-provided output
buffer, returning either the bytes written or an explicit insufficient-space error.

The API must answer:

- Who owns each buffer after success and failure?
- Can output alias input?
- Is allocation forbidden or merely optional?
- Can cleanup block?
- What makes its maximum work and stack bounded?

Zig encourages asking where the bytes are. Fibril should additionally express and
check ownership/resource obligations where justified. No encoder API or syntax is
defined by this example.

## Lessons we should adapt, not copy

### Optimization must not silently remove guarantees

Zig distinguishes Debug/ReleaseSafe from ReleaseFast/ReleaseSmall safety defaults.
For Fibril, borrow the explicit build-profile concept, **not** an implicit weakening
of safe-language semantics in optimized builds.

Checks may be removed when their preconditions are established, or under an
explicitly unsafe contract. Optimization settings must never bypass kernel checks.
A future fast-math mode would also need explicit semantics, not invalidate proofs
about strict arithmetic silently.

### No universal undefined value in trusted proofs

Zig's undefined and unreachable serve low-level programming purposes. Fibril
must not admit an arbitrary inhabitant or an unchecked impossible branch as a
trusted proof. Panic/nontermination belongs behind defined computational
boundaries; logical absurdity requires valid evidence.

### Compile-time convenience needs limits

Specialization and reflection can increase compile time, code size, and resource
use. Prefer deterministic, checked, inspectable mechanisms with explicit budgets.
Do not add another unrestricted metaprogramming system just because Zig has
comptime; first determine what dependent functions and checked elaboration provide.

### Explicit memory management is not automatic memory safety

Zig requires programmers to respect ownership/lifetimes. Fibril's proposed linear
and borrowing features should strengthen those guarantees rather than merely
document them. Exact usage alone still does not establish pointer validity,
aliasing rules, cleanup, or hard-real-time behavior.

### Avoid premature low-level tuning

Zig's reference warns that forced inlining/unrolling can harm performance and
should be justified by semantics or measurements. Apply the same discipline to
Fibril: benchmark before adopting arenas, hash-consing, caching, or specialization.

## Priorities

1. Add reproducible checker/algebra benchmarks and maintain explicit failures.
2. Specify storage, error, and cleanup contracts before embedded libraries.
3. Design target/ABI metadata before native FFI and compilation.
4. Keep optimized-build semantics and proof trust invariant.
5. Add failure-injection and backend differential tests when infrastructure exists.

These complement the [safety/performance plan](safety-performance.md); no Zig
dependency, backend switch, allocator implementation, or new language feature is
introduced by this document.
