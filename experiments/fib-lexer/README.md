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
whole `scan` body, and even an empty input exhausts its 4096-step maximum. Only the native
backend runs it.

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
- Declarations must precede their uses. A linear `String` can't be reused, so it is returned
  out of the `primUTF8Case` branch (`sliceText`) before `keyword` compares it 27 times.

## Budgets: the real blocker

With the stock native runtime (`runtime/native/fibril_runtime.c`: 100000 steps, depth 512,
16 MiB allocation) on prefixes of `Std/List.fib`:

| input | steps | depth | allocation |
| --- | --- | --- | --- |
| 16 bytes | ok | ok | ok |
| 32 to 256 bytes | fail | fail | ok |
| 512 bytes and up | fail | fail | fail |

So the lexer handles about 16 bytes as shipped. Each limit was raised in a temporary copy of the
runtime (`--raise-budgets`) to get the corpus result above; with them lifted a 3.5 KB file lexes
in about 0.3 s. Time per doubling of input is x2.5 to x2.8, closer to quadratic than linear:
the position is a unary `Nat`, so every byte read costs O(position). `Word` positions would
fix that but `primBytesIndex` takes a `Nat`.
