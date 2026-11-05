# IO roadmap

Status: proposal. Branch: `feature/qtt`.

Fibril's core already treats IO as pure descriptions of effects (`IOType`,
`IOPure`, `IOBind`, `WriteLine` in `Core/Term.idr`) and carries QTT quantities
on binders. This roadmap finishes IO on top of that substrate and fixes the
gaps that Idris 2's IO leaves open, without overcommitting to multi-backend
or concurrency design.

## Phase A — basic IO end-to-end

Goal: a program `main : IO Unit` that prints a line via the C backend.

- Elaboration surface for `IO`, `pure`, `>>=` / `do`, `writeLine`.
- Reduction: `IOBind` / `WriteLine` are neutral under `Reduction.idr` and
  `WeakHead.idr`. No β through an action, no CSE across binds.
- Erasure: `Core/Erased.idr` does not drop `IO` actions, even at result type
  `Unit`. Drives Idris 2 gap (9).
- Runtime driver in `Core/Runtime.idr` and the C emitter: walk the IO tree,
  `IOPure` returns, `IOBind` sequences, `WriteLine` lowers to `puts`.
- `main` entry point hook.
- Tests: golden-output test for a hello-world program.

## Phase B — linear world token

Goal: exactly-once effect execution guaranteed by the type system. Fixes
Idris 2 gap (1).

- Represent IO as `World -o (a, World)` or keep the current ADT and require
  quantity 1 on the continuation in `IOBind`.
- Prefer the latter: no new type former, just a quantity choice on an
  existing one. The QTT substrate already enforces it via `Core/Usage.idr`.
- Tests: reject double-bind of the same action; reject discarded IO.

## Phase C — typed exceptions

Goal: `IO e a` with `e` as a typed error channel. Fixes Idris 2 gap (6).

- Add an error-type parameter to `IOType`.
- Primitives: `throw : e -> IO e a`, `catch : IO e a -> (e -> IO f a) -> IO f a`.
- Runtime: a thrown value propagates up `IOBind` until a `catch` frame.
- Tests: throw across binds; catch recovers; uncaught throw aborts `main`.

## Phase D — pure interpreter for testing

Goal: run an `IO e a` symbolically against a scripted environment. Fixes
Idris 2 gap (10). Trivial once A–C are in, because IO is a free structure.

- A function `runPure : Script -> IO e a -> (Log, Either e a)` in the core.
- `Script` provides canned responses for input primitives.
- Tests use `runPure` instead of real IO.

## Phase E — small typed FFI with linear handles

Goal: foreign calls with checked signatures and linear ownership of foreign
resources. Partially fixes Idris 2 gap (3). Explicitly refuses a general
`%foreign` escape hatch.

- Typed declaration form: argument and return types drawn from a fixed set
  (Int, String, opaque `Handle a` with linear ownership).
- Handles carry quantity 1; `close : Handle a -o IO e Unit`.
- No marshalling for dependent types in v1; no callback into Fibril from C.

## Explicitly out of scope

- Row-of-effects or graded effect sets (Idris 2 gap 2). Revisit only if users
  ask.
- Multi-backend semantic parity (gap 5). Fibril has one backend today;
  specify IO's operational semantics in docs and treat divergence as a bug
  when a second backend lands.
- Structured concurrency, cancellation, async (gap 7). Research-grade; ship
  single-threaded IO first.
- `unsafePerformIO` / `believe_me` (gap 4). Not adding them. Ever.

## Order of work

A → B → C → D → E. Each phase is its own PR against `feature/qtt`. B and C
are independent after A; D requires C; E is independent of B/C/D but easier
after B (for handle linearity).
