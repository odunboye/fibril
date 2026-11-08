# Word: unsigned 64-bit machine integers

Status: **checked and evaluated in the reference checker/evaluator only.** There is
no native C lowering yet: `emit-c` rejects any program that uses a Word primitive.

## Use cases

Unary `Nat` costs one successor per unit, so a value like a port, a byte count, a
timestamp or a counter cannot be computed at realistic sizes (see the measurements
in [binary numbers](binary-numbers.md)). `Word` is a primitive type whose arithmetic
is one reduction step regardless of magnitude.

```fibril
mix : (seed : Word) -> Word
mix seed = primWordAdd (primWordMul seed 1000000007w) 998244353w

main : Bool
main = primWordLt (mix 3w) (primWordSub 0w 1w)
```

`fibril eval examples/core/word-arithmetic.fib` normalizes to `True`.

Choose `Word` for counters, sizes, identifiers and hash-style mixing where wraparound
is acceptable or intended. Keep `Nat` where you need structural recursion or
pattern matching: Word has no eliminator and cannot drive `natRec`.

## Surface

| Name | Meaning |
| --- | --- |
| `Word` | Erased type in `Type 0` |
| `123w` | Literal; the suffix must touch the digits, no leading zeros, at most 18446744073709551615 |
| `primWordAdd`, `primWordSub`, `primWordMul` | `Word -> Word -> Word`, wrapping modulo 2^64 |
| `primWordEq`, `primWordLt` | `Word -> Word -> Bool`, unsigned |

Operands are **unrestricted**: Word is copyable data, so `primWordAdd x x` is accepted.
Plain numerals stay `Nat`; there is no implicit conversion either way.

## Design

Words are the first use of the table-driven `Prim : PrimOp -> List (Term n) -> Term n`
core form. A new primitive adds a `PrimOp` row, its arity/result type in the checker,
and its reduction in `evalPrim`; it does not add a constructor to every core pass.
Renaming/substitution proofs cover `Prim` once for all operations.

An out-of-range literal is rejected both by the elaborator and by the independent core
checker, so a hand-built term cannot smuggle one in.

## Not provided

No division, remainder, shifts, bitwise operations, `Nat`/`Word` conversion or signed
variant; no `Word` in records of native programs; no native lowering; no overflow
detection (wraparound is the only semantics). Each is a follow-up, not a guarantee.
