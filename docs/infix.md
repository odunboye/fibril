# Named infix calls

## Use cases

Use backticks when placing a two-input operation between its operands improves readability: `appendString left right` and ``left `appendString` right`` compute the same thing.

Generic methods also work: ``left `combine String @{implementation}` right`` combines through a selected dictionary. Prefer prefix calls when long type/dictionary arguments make infix harder to read. This adds no computational power and does not prove the operation associative; chains group left.

**Implemented prototype:** backticks put an ordinary function application between
two operands:

~~~fibril
"Hello" `appendString` ", world!"
left `combine String @{implementation}` right
left `combine A @{}` middle `combine A @{}` right
~~~

[The runnable graph](../examples/modules/infix/Main.fib) exercises generic
String/Bool operations and a Monoid dictionary. The functions are ordinary
checked declarations; the parser does not recognize appendString, combine or any
other library name specially.

![Named infix lowering](diagrams/infix.svg)

## Precedence and association

All backtick calls share one precedence and associate **left**:

~~~text
a `f` b `g` c      means g (f a b) c
f a `g` h b        means g (f a) (h b)
a `f` (b `g` c)    means f a (g b c)
~~~

Ordinary application and dictionary selections bind tighter. Function arrows
bind looser. Conditional, let, lambda and case forms retain their existing
syntax; use parentheses when such a form is an operand or function expression.

Between the backticks is an application expression: a local/qualified function,
its explicit type/dictionary arguments, or a parenthesized expression producing
a function. Nested calls can appear inside those parentheses.

~~~fibril
"a" `(if flag then appendString else backwards)` "b"
~~~

No precedence is inferred from the function name. User fixity declarations,
user-defined symbolic operators (only the fixed Word `+ - *`, see [words](words.md)), sections and implicit overloaded-method insertion are not
implemented. A missing argument or inappropriate function type fails ordinary
checking rather than acquiring a special operator meaning.

## Elaboration and resources

Authored NInfix syntax retains the actual function and operand spans. Expression
elaboration emits exactly Apply (Apply function left) right. It does not copy an
operand, invent implicit arguments, reorder source effects or extend conversion.
Compilation/checking remains effect-free; external effects still require the
separate complete checked IO plan.

The ordinary checker enforces the function's parameter quantities. A linear
operand mentioned twice fails, and an erased global used as the runtime operator
still fails on the original signature-preserving occurrence. There is no
normalization step to evade either check.

Project pre-clone admission counts both generated applications and all three
subexpressions. Parser fuel bounds chains, and the independent core count remains
in force. These are admission policies, not a new soundness/resource theorem.

## Source tools and evidence

The actual operator-name token participates in definitions, references and
lexical rename previews. No synthesized symbol is used. Syntax-only elaborate
PATH reports infix-apply and remains unchecked.

Formatting reparses and checks AST shape, keeps simple quoted calls tight, tracks
nested grouping/quotes, and can wrap a long expression before a backtick call.
It preserves literal/comment spelling and association; the existing safe
fallback and do-block restrictions remain. Vim/Neovim recognizes backticks as
punctuation. Formatting never saves a buffer automatically.

Tests exercise left-versus-right NAND association, application precedence,
parenthesized nested function expressions, generic imported methods, literal
backticks, formatter idempotence and long wrapping, operator definition/rename,
linear/erased rejection, malformed input and chain-budget exhaustion.

**Remaining:** symbolic operator declarations and scoped fixity policies need a
separate design; this slice adds only general quoted function application.
