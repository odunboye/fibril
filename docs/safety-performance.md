# Safety and performance from the outset

Status: engineering policy and proposed work, not established language guarantees.
Some safeguards and an exploratory benchmark suite exist; enforceable resource
isolation and stable performance guarantees do not.

## Safety discipline

- Keep trusted checking independent of editors, tactics, orchestration, and backends.
- Never accept exhausted evaluation, unresolved obligations, or unsupported constructs.
- Distinguish logical consistency, runtime memory safety, resource policy, and timing.
- Track future axioms, partial definitions, unsafe code, and FFI assumptions explicitly.
- Justify quantitative/cubical interactions and erasure before relying on them.
- Combine negative tests, constructive properties, review, and eventual formal proofs.
- Later test generated C with applicable sanitizers and compare C/JS semantics.
- Preserve checked source semantics in optimized builds: optimization must not
  silently weaken proof checking or turn safe operations into undefined behavior.

Implemented examples include scope indices, explicit budget errors, negative
checking tests, and Hedgehog properties. These do not establish full soundness.

## Performance discipline

Establish reproducible benchmarks before optimizing:

- Substitution/renaming over increasing term size and binder depth.
- Reduction/conversion with normal, reducible, and exhausted inputs.
- Erased/runtime checking over increasing context depth and dependent terms.
- Interval equality and face entailment, including adversarial DNF growth.

Record input size/shape, repetitions, warmup, machine/OS, compiler/collection,
code generator, options, and revision. Separate build time from execution.
Measure elapsed time and, where tooling supports it, allocations/peak memory.
Do not claim unavailable metrics. Use stable baselines before enforcing regression
thresholds; avoid timing gates sensitive to noisy CI machines.

Profile first. Keep simple reference implementations for differential checks.
Benchmark a proposed improvement alongside correctness tests. Optimize whole
workflows as well as isolated functions; don't trade maintained invariants for
unmeasured speed or needless abstractions.

## Known current risks

| Area | Risk | Candidate investigation, not implemented optimization |
| --- | --- | --- |
| Interval/face DNF | Exponential normal-form growth | Work/node budgets and alternative symbolic representations |
| Substitution | Copies syntax and can enlarge terms | Sharing, environments, or delayed substitution |
| Runtime analysis | Repeats erased inference/context formation | Reuse checked evidence with a clear trust boundary |
| Type exposure | Full normalization when only Pi/Universe head is needed | Weak-head evaluation with regression/differential tests |
| Fuel | Does not bound wall time, stack, or memory | Cancellation, work budgets, process isolation where needed |

An [exploratory benchmark suite](benchmarks.md) now measures these operations
and validates results. Initial DNF workloads show steep growth; tiny term workloads
remain close to harness overhead. No stable performance baseline exists yet.
Candidate optimizations still need measured evidence.

## Untrusted inputs and real time

A total host function can still consume excessive memory/time. Future public
services need enforced limits and cancellation, especially symbolic solvers,
parsers, plugins, and normalization. Limits must fail explicitly, never accept a
proof obligation. Harden these boundaries before offering an untrusted service.

Hard-real-time guarantees require target/application-specific timing, blocking,
and interference evidence. Checker speed, totality, GC avoidance, and linearity
do not establish deadlines.

## Completion checklist for future optimizations

1. Name the bottleneck and measurement.
2. State preserved semantics and trust assumptions.
3. Add adversarial and differential tests.
4. Record before/after results and any memory trade-off.
5. Update documentation and commit independently of unrelated feature changes.

See [testing](testing.md), [guarantees](guarantees.md), and
[Zig lessons](zig-lessons.md).
