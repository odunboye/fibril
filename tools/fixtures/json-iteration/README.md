# Buffered JSON iteration diagnostic

Source-only adoption on accepted foundations; not a production JSON library.
See `docs/json-iteration-adoption.md` for API/effects, evidence and limitations.

- `Protocol/JSON.fib`: one pure transition/finalizer, pure Nat-fold API and
  explicitly binary-effectful already-buffered `parseJSONBinary` API.
- `Parse.fib`, `ParseBinary.fib`: API admission measurement entries.
- `PureRead65.fib`, `Read65.fib`: diagnostic clients, not framing. Read at most65
  bytes to test the64-byte policy. They do not detect an additional unread suffix.
- `Hosted.idr`, `SourceHarness.c`: test adapters/counters, never JSON parsers.

`tools/test_json_iteration.py` stages only a private library, checks/emits the
actual source, compares against the duplicate-preserving Python oracle, and
instruments private copies without changing runtime decisions or limits. Its
short-allowance and control-bypass variants are test-only negative/cost controls.
All accepted historical `json-admission` fixtures remain intact.
