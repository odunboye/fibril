# Blocked JSON admission diagnostics

These are **not working examples, production modules or regression tests**.
See `docs/binary-json-blockers.md` for the measured admission/backend blockers,
prototype API, token encoding and unvalidated limits.

- `full/Parse.fib`: check/measure the single pure parser body.
- `full/Main.fib`: minimal 16-byte binary consumer; exceeds entry admission.
- `scalar/Main.fib`: reduced number/bool/null consumer; hosted `1` works, native
  emission rejects the record's pair operations in Binary mode.
- `Measure.idr`: read-only checked-core size/payload observer, compiled against
  this worktree's staged library by `tools/observe_json_admission.py`.

Do not add these fixtures to normal working-example discovery. The observation
tool reports current behavior and does not require failures to remain permanent.
