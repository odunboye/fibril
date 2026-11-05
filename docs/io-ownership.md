# Proposed IO ownership contract

Status: source ownership remains a design proposal, not a soundness claim.
A [host-only scoped input-file pilot](io-scoped-files.md) now implements cleanup
and lease revocation, but not source-level linear handles.

## Preserve the distinction between descriptions and execution

Current `IO A` values describe computation. Unrestricted bindings can duplicate
or discard descriptions; doing so is not itself a host effect. Bind's linear
result parameter constrains consumption of the returned value, not the number
of times a reusable description can be executed.

Retain that behavior for existing console programs. Do not relabel it as
world-token IO. Introduce resource-sensitive operations only after the following
separate capability contract has been implemented and tested.

## Current action-binding regressions

Source tests now distinguish unrestricted descriptions from explicitly linear
action bindings: an unrestricted `IO ReadResult` binding may be discarded or
reused; a quantity-1 binding rejects both discard and reuse. These are checked
usage rules on bindings, not an intrinsically linear IO type or an exactly-once
external-execution guarantee. They provide a baseline for future handle tests.

## Resource-sensitive API requirements

- A trusted host operation creates each resource capability. Pure source code
  cannot forge one or obtain it from an erased argument.
- Each operation consumes its input capability and returns a successor
  capability, or closes it. Duplicating or silently dropping a live capability
  must be rejected.
- The runtime boundary owns the initial execution capability. It is not exposed
  as a freely reusable source value; normalization cannot execute it.
- An action capturing a linear capability cannot be promoted to unrestricted
  use. Check this through closures, containers, helpers and module boundaries.
- Failure must either return ownership to the caller or transfer it to a
  cleanup mechanism. Catching an error cannot silently lose captured resources.
- Foreign code remains trusted to honor ownership and lifetime contracts.

A linear world parameter is one possible representation, not a complete solution
by itself. The implementation must specify how action closures and resource
results are tracked, how the runner invokes them, and which cleanup guarantees
hold under represented errors versus process termination or foreign faults.

## Required evidence before enabling resource primitives

Positive tests: transfer, sequential use, explicit close, branch-balanced use,
closure capture and recovery with retained ownership.

Negative tests: duplicate execution of a resource-capturing action, dropped live
handles, double close, erased extraction, unrestricted capture, and skipped
cleanup on an exceptional path.

Test both hosted and native execution. State operational behavior for partial
output and cleanup failure. No claim of exactly-once external execution under
crashes or OS failures follows from source-level linearity.
