# Abstract size-change certificates

## Status and use case

**Experimental foundation, not language termination checking.**
`Fibril.Termination.SizeChange.verify` independently checks a proposed closure
for a caller-supplied abstract call graph. It is useful for exercising the
finite graph criterion and a future producer/checker boundary. No parser,
elaborator, recursive core term, evaluator, CLI or backend calls it. **It does
not authorize any new recursive Fibril program.** Existing structural equations
continue to lower to independently checked recursors.

![Abstract size-change trust boundary](diagrams/size-change-certificates.svg)

## Graph and certificate

Functions are numbered by position in an arity list. A call edge `f -> g` has
one row per argument of `g` and one column per argument of `f`. Each cell is:

| Cell | Supplied assertion about the callee argument relative to the caller argument |
|---|---|
| `Unknown` | No ordering established. |
| `NonIncreasing` | No larger. |
| `Decreases` | Strictly smaller. |

For example, a one-argument self-call with `[[Decreases]]` passes when its
certificate contains that edge. A self-call with `[[NonIncreasing]]` does not.
This says nothing about whether either assertion describes a real call.

A supplied certificate is a finite **set of distinct matrices**, identified by
both endpoints and cells. The checker validates endpoint/row/column shapes,
requires every direct call to be present, and checks closure under every
compatible pairwise composition. For a composed cell, it considers each
intermediate argument: a chain with an unknown relation establishes nothing;
otherwise a chain is strict if either component is strict. When several
intermediate arguments establish relations for the *same composed call*, the
strongest relation wins. Different call edges or paths remain distinct matrices:
merging alternative calls into one stronger matrix would be unsound.

Finally, every self-edge in the certificate that is idempotent under composition
must have a strict diagonal cell. A zero-argument self-cycle therefore fails.
The certificate may include extra edges, but those edges must also satisfy the
closure and cycle checks. This is the finite idempotent form of the size-change
criterion; see Lee, Jones and Ben-Amram, *The Size-Change Principle for Program
Termination* (POPL 2001).

`GraphAccepted` means only that these checks succeeded for the supplied abstract
graph and certificate. `GraphRejected` means the supplied certificate or graph
criterion failed; it does **not** prove that a program diverges. An admission
limit returns `GraphInconclusive`, never acceptance.

## Trust and future integration

The checker cannot establish that the supplied direct graph contains every real
call, that its edges describe the actual arguments, or that a strict cell is
true. To use this criterion for programs, future work must independently tie
complete call extraction and each relation to the **exact checked recursive
bodies**, account for higher-order and mutual calls, and establish suitable
well-founded orders and compatibility of the strict/non-increasing relations
across every composed argument. Recursive definitions, positivity, dependent
conversion, quantitative use, execution and backend support also need explicit
checked designs. A producer's metadata or a graph verdict cannot substitute for
those obligations.

The finite tests are sampled implementation evidence. They include exhaustive
three-relation algebra, rectangular composition orientation, alternating and
mutual descent, missing or non-closed certificates, conflicting alternative
calls, malformed shapes, zero-argument cycles and admission failures. They are
not a mechanized proof of the size-change theorem, termination of Fibril terms,
whole-language soundness or compiler correctness.

## Admission

This first checker admits at most 16 functions, 8 arguments per function, 128
direct edges and 32 certificate edges. Matrices are checked against those arities
before composition. These are explicit admission policies; they do not prove a
hard bound on host memory, stack, elapsed time or allocation. The certificate
producer and any closure-generation algorithm are not implemented yet.
