# IO roadmap

Status: proposal. Branch: `feature/qtt`.

Fibril's core already treats IO as pure descriptions of effects (`IOType`,
`IOPure`, `IOBind`, `WriteLine` in `Core/Term.idr`) and carries QTT quantities
on binders. A read of the current tree shows that most of what an earlier
version of this document called Phase A and Phase B is **already in place**
on `master`. The sections below have been revised to reflect that.

## Already shipped

- **Typing** (`Core/Erased.idr`): rules for `IOType`, `IOPure`, `WriteLine`,
  `IOBind`. The continuation in `IOBind` is required at quantity `Linear`,
  which gives the exactly-once discipline the Phase B section used to call
  for.
- **Reduction** (`Core/WeakHead.idr`): monad left identity
  (`IOBind a b (IOPure v) k ⇒ Apply k v`); `IOBind` is otherwise neutral
  and only steps under the action it is sequencing. Erasure/CSE through an
  action is structurally prevented.
- **Runtime usage** (`Core/Runtime.idr`): usage rules for `IOPure`,
  `WriteLine`, `IOBind` that combine action and continuation usage.
- **Host effect model** (`Fibril.Effect.Console`): `ConsoleAction = PrintLine
  String`.
- **Driver** (`Fibril.Driver.Run`): `prepareIO` extracts a list of console
  actions from a checked `main : IO Unit`; `executeConsoleActions` performs
  them. Entry points: `runProject`, `runPackage`, `runFile`.
- **C backend** (`Fibril.Driver.Native`): `IOPure`, `IOBind`, `WriteLine`
  lower to `f_pure`, `f_bind`, `f_write`; `emitCheckedC` validates the entry
  against `IOType UnitType` before emitting.

## Phase C — richer primitive effects

The primitive effect set today is just `WriteLine`. Typed exceptions earn
their keep only once there are effects that can fail, so these come first.

- `ReadLine : IO String` (and define EOF behavior explicitly in docs).
- `GetArgs : IO (List String)`.
- Optional: environment lookup, time, exit code.
- Driver: extend `ConsoleAction` with request/response variants or switch
  to a small free-monad interpreter in `Fibril.Effect.Console`.
- C backend: corresponding `f_read_line`, `f_get_args` primitives.
- Tests: golden tests for each new primitive.

## Phase D — typed exceptions

Goal: `IO e a` with `e` as a typed error channel. Fixes Idris 2 gap (6).

- Add an error-type parameter to `IOType` (migration touches every IO
  constructor's typing rule and every backend case).
- Primitives: `throw : e -> IO e a`,
  `catch : IO e a -> (e -> IO f a) -> IO f a`.
- Reduction: `catch` reduces when its argument is `IOPure` (success) or a
  `throw` at the head; otherwise steps inside the argument. `IOBind` must
  propagate a `throw` past the continuation.
- Runtime: a thrown value propagates up `IOBind` until a `catch` frame; an
  uncaught `throw` at top level aborts `main` with the error rendered.
- Tests: throw across binds; catch recovers; uncaught throw aborts `main`.

## Phase E — pure interpreter for testing

Goal: run an `IO e a` symbolically against a scripted environment. Fixes
Idris 2 gap (10). `prepareIO` is close to this already but is specialized to
`PrintLine` and doesn't model input or exceptions.

- Generalize to `runPure : Script -> IO e a -> (Log, Either e a)`.
- `Script` provides canned responses for input primitives.
- Tests use `runPure` instead of real IO.

## Phase F — small typed FFI with linear handles

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

C → D → E → F. Each phase is its own PR against `feature/qtt`. E depends on
D; F is independent and can land in parallel.
