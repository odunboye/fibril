# Symbolic operators and fixity

## Use cases

Use an operator when an infix form reads better than a prefix call and the operation is
used often enough that a name would be noise (`a + b`, `xs ++ ys`). For a one-off helper,
or when the operation has no widely understood symbol, a named function is clearer.

**Implemented prototype:** symbols are ordinary names, infix chains are grouped by declared
fixity, and `+` can be overloaded through [inferred dictionaries](constraints.md#inferred-dictionaries-after-implicit-arguments).
No library name is known to the compiler.

~~~fibril
infixl 6
export
(+) : {0 A : Type 0} -> (ops : Add A) => (left : A) -> (right : A) -> A
(+) = \(0 A : Type 0) => \(ops : Add A) => \(left : A) => \(right : A) => add A @{} left right
~~~

See [the example](../examples/modules/operators/Main.fib).

## Names

A maximal run of `+ - * / < > & ^ ! ~ % $ ? # @ = | :` is an operator token. `(op)` written
with no spaces is a name, so `(+)` defines, references, exports and imports like any other
function, and `(+) 40w 2w` is the prefix form. A bare leading `+ 1 2` is not a call.

These runs keep their fixed meaning and are never operators: `=`, `|`, `:`, `->`, `<-`,
`=>`, `@{`, and `--` (a comment) at the start of a run. `.`, `\`, `,`, brackets and the
backtick are excluded from operator names, because they already mean module paths, lambdas,
separators and named infix calls.

## Fixity

`infixl N`, `infixr N` or `infix N` (N from 0 to 9, higher binds tighter) stands alone on
the line before the one declaration it describes, like `requires`. `export` may come before
or after it. Fixity belongs to the declaration, is stored with the global and travels with the
name through exports and imports. `infixl` and `infixr` group equal-precedence neighbours left
or right; `infix` never chains.

- An operator without a declaration is `infixl 9`, the same as a backtick call.
- Equal-precedence neighbours with different grouping (`infixl 6` beside `infixr 6`), and any
  chain of non-associative operators, are errors that ask for parentheses.
- Application binds tighter than every operator; function arrows, conditionals, lambdas, `let`
  and `case` bind looser, so parenthesize them as operands.
- A fixity line before anything but an ordinary function declaration is an error.

## How it works

The parser records a flat chain of operands and operator tokens. Grouping needs the fixity of
imported names, which is only known during module checking, so each declaration is rewritten
there, just before elaboration, into plain `Apply (Apply (+) a) b` calls. Everything after that
(implicit arguments, dictionary insertion, the core checker) sees ordinary applications.
No core term, conversion rule or runtime support is added. The formatter, navigation and the
elaboration printer work on the unrewritten chain.

## Limits

- Operators work in named modules. A bare expression or single declaration file reports that
  a module is required, because its fixities cannot be known.
- Interface types are still structural. Two interfaces with the same method shape cannot be
  told apart by dictionary lookup, so `Add` and `Sub` over one type with identical methods
  would be ambiguous. Overload an operator through an interface whose shape is unique, or use
  an ordinary function. Nominal interface identity is separate future work.
- No sections (`(+ 1)`), unary minus, qualified operator syntax, or overloaded numeric literals.
- Operators inside data, record and mutual declaration headers are not yet grouped.
- `Nat` arithmetic is not provided: a unary `Nat` makes `+` look cheap when it is not
  (see [binary numbers](binary-numbers.md)).
- Editor highlighting does not yet colour operator tokens.
