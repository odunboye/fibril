# Recursion tour

An index of the runnable recursion examples, grouped by how the compiler accepts
them. Each linked program has its output checked by `tools/test_native.py` or
`tools/test_cli.py`, so none is duplicated here.

## Structural forms lowered to existing checked recursors

These are not general recursion and do not use the size-change checker: each
accepted equation lowers to an independently checked recursor or fold. Run any of
them from the repository root after `make build`:

```sh
./build/exec/fibril run --source-dir examples/modules/mutual-parity examples/modules/mutual-parity/Main.fib
```

- [Mutual parity](../mutual-parity/Main.fib): two workers descend on a Nat
  predecessor.
- [Forwarded linear Bool](../mutual-parity/Payload.fib): both workers pass the
  same linear Bool along with the predecessor.
- [Reordered arguments](../mutual-parity/Reordered.fib): one worker forwards with
  swapped arguments, the other descends.
- [Linear list accumulator](../linear-accumulator/Main.fib): reverses a list onto
  an accumulator that changes at every step.

See [bounded mutual structural equations](../../../docs/mutual-structural-equations.md)
and [recursive groups](../../../docs/recursive-groups-design.md) for the exact
restrictions.

## General recursion checked by size-change

When no structural form applies, a self-referencing equation is accepted only if
the size-change gate proves some argument decreases:

- [Half](../general-recursion/Half.fib): steps down by two.
- [Swap](../general-recursion/Swap.fib): accepted only because two calls together
  decrease.
- [Loop](../general-recursion/Loop.fib): refused, because the call rebuilds its
  input.

See [general recursion](../../../docs/function-equations.md#general-recursion).
