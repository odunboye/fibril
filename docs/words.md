# Word: unsigned 64-bit machine integers

Status: checked, evaluated by the reference runner, and lowered to C by `emit-c` in
every native mode. The [JavaScript backend](javascript.md) uses exact `BigInt`
operations for its output-only fragment. `primWordToString` formats a Word as decimal text, so Words can be
printed (see `examples/core/word-native.fib`).

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
| `primWordDiv`, `primWordRem` | `Word -> Word -> WordDivResult`: unsigned quotient/remainder, or a divide-by-zero value |
| `primWordDivCase` | `(0 A : Type 0) -> (1 r : WordDivResult) -> (byZero : A) -> (ok : Word -> A) -> A` |
| `primWordFromNat` | `(1 n : Nat) -> Word`: the Nat's value modulo 2^64 |
| `primWordToString` | `Word -> String`: decimal digits only (`0`, `8080`, `18446744073709551615`); no sign, padding or separators |

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

`primBytesWordAt` reads a byte at a `Word` position (see [bytes](bytes.md)). No shifts, bitwise operations, `Word`-to-`Nat` conversion, String-to-Word parsing, hex or padded formatting, or signed variant; no overflow detection (wraparound is the only
semantics). Each is a follow-up, not a guarantee.

## Division and conversion

Division by zero is **not** a runtime failure and not a stuck term: `primWordDiv` and
`primWordRem` return a `WordDivResult`, a two-arm variant (tag 0 divide-by-zero, tag 1
the Word result), and `primWordDivCase` eliminates it. This keeps every Word operation
total, the same way `primBytesIndex` returns a missing/found result instead of failing.

```fibril
safeDiv : (a : Word) -> (b : Word) -> String
safeDiv a b = primWordDivCase String (primWordDiv a b) "divide by zero"
                (\(q : Word) => primWordToString q)
```

`primWordFromNat` is total because it wraps: a Nat above 2^64-1 becomes its value modulo
2^64. It costs one step per successor, so converting a large unary Nat is only as cheap
as having built that Nat; use `5w` literals for constants. There is deliberately no
`Word`-to-`Nat` conversion, since it would expand a 64-bit value into unary.

## Native lowering

A Word is a tagged `uint64_t` value in the lazy runtime; `+ - *` use C unsigned
arithmetic, so wraparound is defined behavior and equals the reference evaluator's
modulo-2^64 rule. Literals are emitted as `UINT64_C(<decimal>)` after the emitter
re-checks the range. `tools/test_native_words.py` compiles with `-Wall -Wextra -Werror
-pedantic` (and ASan/UBSan with `FIBRIL_WORD_SANITIZE=1`) and requires native output
to equal `fibril run` output. That is sampled differential evidence, not a proof of
semantic preservation. Word values still run under the shared native step/depth/memory
budgets.
