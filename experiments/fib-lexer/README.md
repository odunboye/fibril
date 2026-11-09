# A Fibril lexer written in Fibril

`src/Fib/Lexer.fib` tokenizes Fibril source held in a `Bytes` value, following
`Fibril.Source.Lexer.scan`. `src/Main.fib` reads one stdin chunk (at most 4096 bytes) and
writes one line per token, `START-END KIND`, with half-open **byte** offsets. A lexical
error ends the output with `OFFSET error`.

Experiment, not a feature: nothing outside this directory is changed.

## Run it

```sh
F=build/exec/fibril            # or any built fibril
$F emit-c-binary --source-dir src src/Main.fib > /tmp/lex.c
cc -std=c11 -I ../../runtime/native /tmp/lex.c ../../runtime/native/fibril_binary_runtime.c -o /tmp/lex
printf '(\\x => x)' | /tmp/lex        # 0-1 (  /  1-2 lambda  /  2-3 name  /  4-6 =>  /  7-8 name  /  8-9 )
```

`fibril eval`, `run` and `run-binary` cannot run it: the reference evaluator normalizes the
whole `scan` body, and even one byte of input exhausts its 4096-step maximum. Only the native
backend runs it. It needs a compiler that has `primBytesWordAt` (this branch).

## Differential test

```sh
python3 diff_lexer.py --fibril build/exec/fibril --raise-budgets fixtures ../../examples ../../stdlib
```

`--raise-budgets` builds against a temporary copy of `runtime/native` with the step, depth and
allocation caps lifted (the repo's runtime is not modified); without it the stock caps apply and
anything over about 16 bytes fails. Result: 194 match, 0 mismatch, 2 files skipped for exceeding
the 4096-byte chunk.

It compares `(start, end, kind)` against `fibril lex-source` (scalar line:col converted to byte
offsets). A file with a sibling `.expected` is compared to this lexer's exact output instead;
`fixtures/errors/` uses that for inputs the reference rejects (unterminated string, unexpected
character, an embedded NUL). Exit status is nonzero for any mismatch, native budget failure or
crash, or if nothing was compared; `--allow-partial` tolerates budget failures.

The harness applies the `(op)` name collapse to this lexer's output, as the Idris lexer does after
scanning, so a passing comparison covers the lexer plus that post-pass.

Not ported: string-escape validation (`"\q"` is accepted), source-control validation (a NUL is
rejected everywhere, including inside comments and strings, but other controls are not) and line/column tracking.
Input beyond one 4096-byte chunk is reported (`input exceeds 4096 bytes`), not lexed. Running out
of scan fuel is reported as `OFFSET error`.

## What the language forced

- **A recursive function cannot take a `Bytes` parameter.** The size-change gate refuses it
  (`unsupported term form in a recursive body: Bytes`; `Word` and `String` are fine). The
  recursion takes a reader closure `rd : (p : Nat) -> Word` instead.
- **A recursive function cannot call another recursive function** (a nested `Fix` is refused).
  So there is one flat state machine (`scan`, modes 0/2/3/4/5/6/7) rather than `scan` plus
  `skipWhile`. Each run ends by emitting its token and re-reading the same byte, so the fuel
  is `2 * length + 3`.
- A recursive call under a two-binder immediately applied lambda is refused as "non-leading";
  nesting the lets one binder at a time is accepted.
- **The native backend admits at most 8192 core nodes.** The lexer is close to it: adding a
  small stdin-truncation check overflowed it, and the fix was folding the single-byte
  punctuation branches into one helper (`punct`).
- Declarations must precede their uses. A `Word` computed from a linear `Bytes` cannot feed an
  unrestricted operand, so the bytes are shared first (`primBytesShare`, which needs a record, so a
  module) or the use stays inside the branch that owns them.

## Efficiency work (measured)

`measure.py` builds against a copy of the runtime with the caps lifted and reads the
`FIBRIL_STATS=1` line (steps, peak depth, allocated bytes). Corpus: 5 files, 7695 bytes
(`Std/List.fib`, `Std/Bytes.fib`, `Prelude.fib`, `core/identity.fib`, `modules/data/Main.fib`),
startup subtracted:

| version | steps/byte | peak depth/byte | allocated bytes/byte |
| --- | ---: | ---: | ---: |
| before | 626 | 14.0 | 20,428 |
| 1. `if`-tree character classes (short-circuit, common case first) | 388 | 14.0 | 12,599 |
| 2. space, name and digit tested first in the dispatch | 303 | 11.9 | 10,012 |
| 3. name packing branched at the call site (no thunk chain) | 285 | 12.5 | 9,457 |

Net: **-54% steps and -54% allocation per byte**, depth per byte -10% (step 3 traded about 6%
more depth for about 6% fewer steps; the tail-call work removes that term anyway). Each step
kept all 196 corpus and fixture files matching the Idris lexer.

Startup is separate and driver-made: the read capacity is a unary `Nat`. A literal is cheap
(256 costs 582 steps in total) but is capped at 256, so larger capacities are built by doubling
with `natRec`, which costs about 17 steps and 710 bytes of allocation per unit.

| read capacity | startup steps | startup allocation |
| ---: | ---: | ---: |
| 256 | 582 | 29 KB |
| 512 | 5,213 | 223 KB |
| 1,024 | 14,452 | 608 KB |
| 2,048 | 32,907 | 1.4 MB |
| 4,096 (current driver) | 69,794 | 2.9 MB |

That is 70% of the stock step budget and 18% of the stock allocation budget spent before the
first byte is read. Fixing it needs a Word-based read API or chunked input, which is out of
scope here.

## Budgets: which limit bounds what

Positions are `Word`s and bytes are read with `primBytesWordAt` (added to the compiler on this
branch), so a read is O(1); `scan` makes tail calls, which the runtime now runs in constant depth;
and the output string is forced once per iteration, so no chain of deferred appends builds up.
`measure.py` and `diff_lexer.py --raise-budgets` build with the limits lifted (`-DF_MAX_*`, see
`docs/native-c.md`) and read `FIBRIL_STATS=1`.

Resource use per input byte, startup removed (5 files, 7695 bytes):

| | steps | peak depth | allocation |
| --- | ---: | ---: | ---: |
| before any of this work | 626 | 14.0 | 20,428 |
| now | 343 | 0.02 | 11,447 |

Peak depth no longer grows with input: 48 at 36 bytes, 62 at 3992 bytes (it was about 38,000).

Largest input that runs on the **stock** runtime (100000 steps, depth 512, 16 MiB), found by
bisection with only one stock limit applied at a time and the other two lifted:

| driver read capacity | steps only | depth only | allocation only | all three stock limits |
| ---: | ---: | ---: | ---: | ---: |
| 4096 (current `Main.fib`) | 120 | 4074 | 1298 | **120** |
| 256 | 203 (whole chunk) | 203 (whole chunk) | 203 (whole chunk) | **203 (whole chunk)** |

So on the stock runtime the lexer is bound by **steps**, for two separate reasons:

- **Startup.** A 4096-byte read capacity is a unary `Nat` built by doubling, about 70,000 steps and
  2.9 MB before the first byte. That leaves about 30,000 of the 100,000 steps for scanning, which is
  why the current driver stops at 120 bytes. With a 256-byte capacity startup is negligible and the
  whole chunk fits.
- **Scanning itself.** Startup is not the only reason. At about 343 steps and 11 KB per byte, a 4 KB
  file needs about 1.4M steps (14 times the 100,000 default) and about 45 MB of allocation (2.8 times
  the 16 MiB default) even with startup removed. A smaller read capacity cannot fix that; lexing
  real files on the stock defaults needs the limits raised, which an embedder can now do per
  invocation. Depth is no longer a problem.

What would change that: a Word-based read API or chunked input (removes the startup term and the
256-successor literal cap), and fewer evaluator steps per byte (the dispatch is a chain of `if`s
over comparison primitives; a table lookup would need bit or division primitives that do not exist).
