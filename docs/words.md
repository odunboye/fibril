# Word: unsigned 64-bit machine integers

Status: checked, evaluated by the reference runner, and lowered to C by `emit-c` in
every native mode. A Word cannot yet be **printed**: there is no Word-to-String
conversion, so a program observes Words only through `Bool` results such as
`primWordEq`/`primWordLt` branches (see `examples/core/word-native.fib`).

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

No division, remainder, shifts, bitwise operations, `Nat`/`Word` conversion, Word-to-
String formatting or signed variant; no overflow detection (wraparound is the only
semantics). Each is a follow-up, not a guarantee.

## Native lowering

A Word is a tagged `uint64_t` value in the lazy runtime; `+ - *` use C unsigned
arithmetic, so wraparound is defined behavior and equals the reference evaluator's
modulo-2^64 rule. Literals are emitted as `UINT64_C(<decimal>)` after the emitter
re-checks the range. `tools/test_native_words.py` compiles with `-Wall -Wextra -Werror
-pedantic` (and ASan/UBSan with `FIBRIL_WORD_SANITIZE=1`) and requires native output
to equal `fibril run` output. That is sampled differential evidence, not a proof of
semantic preservation. Word values still run under the shared native step/depth/memory
budgets.
