# Guarantees and non-guarantees

Status: intended policy, not implemented guarantees.

- Total by default; explicit partial computation must not establish trusted proofs.
- Quantities 0, 1, and unrestricted are checked statically under rules still to be specified.
- Erasure must preserve observable computation, including relevant transport.
- Axioms, runtime unsafety, and foreign assumptions must remain visible and distinct.
- Foundations are selected project-wide; switching requires rechecking.
- C and JavaScript must preserve specified shared semantics.
- Bare-metal support does not imply bounded timing.
- Hard-real-time claims require target/application-specific evidence.
- Termination, linearity, self-hosting, and kernel size alone do not establish
  consistency, compiler correctness, bounded memory, or deadline guarantees.
