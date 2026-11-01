# Pure String values

Status: implemented primitive String typing, literal data, and pure concatenation
in the ordinary core, with a checked Fibril appendString wrapper. This is not a
complete string library, backend ABI, or general IO/effect system.

## Try a pure program

~~~sh
./build/exec/fibril check examples/core/string-identity.fib
./build/exec/fibril eval examples/core/string-identity.fib
~~~

[The source](../examples/core/string-identity.fib):

~~~fib
identity : (1 text : String) -> String
identity = \(1 text : String) => text

main : String
main = identity "Hello from pure Fibril."
~~~

Evaluation reports Type: String and a quoted normal form. This is pure reference
computation and diagnostic rendering, not execution of putStrLn. run still
requires a runtime-checked main : IO Unit program.

## Chosen ordinary rules

    StringType : Universe 0
    StringValue text : StringType

Both constructors are scope-independent atoms under renaming and substitution.
StringValue contributes zero runtime usage. StringType is a type expression,
not a supported runtime value, like UnitType and BoolType.

Literals have no additional reduction rule. Existing beta/Unit/Boolean computation
can select or pass a literal. Structural conversion compares literal host String
data exactly: distinct text stays distinct, including canonically equivalent
Unicode spellings. No NFC normalization, extensional string equality rule, or
term-level equality function is introduced.

These are explicit local prototype rules. No dependent eliminator, cubical
transport rule, equality reflection, or canonicity theorem follows from them.

## Pure concatenation

~~~fib
appendString : (1 left : String) -> (1 right : String) -> String
appendString = \(1 left : String) => \(1 right : String) => primStringAppend left right
~~~

This definition lives in [stdlib/Prelude.fib](../stdlib/Prelude.fib). It uses normal
resolution/application, can be partially applied or shadowed, and is not special
parser syntax. The small primitive boundary exposes primStringAppend as a closed
linear function constructing the core StringAppend node.

StringAppend left right requires both operands to have String type. Its runtime
usage is their sum; each input is consumed once. Two literal operands contract
to their exact host-text concatenation, with no Unicode normalization:

    StringAppend (StringValue left) (StringValue right)
      --> StringValue (left ++ right)

Full reduction visits operands left-to-right; head reduction forces operands as
needed to expose the resulting literal. One literal concatenation spends one
contraction, regardless of text size. No empty-string or associativity rewrite
is added for neutral operands.

~~~sh
./build/exec/fibril run examples/core/string-append.fib
~~~

[The example](../examples/core/string-append.fib) prints Hello, Fibril! by composing
an ordinary helper, appendString, and putStrLn. check/eval never execute the write.

Duplicating a quantity-1 input with appendString x x is rejected before reduction,
as is extracting an erased input. Unrestricted inputs can be reused. Immutability
does not relax the quantitative rules.

Concatenation allocates host strings. File/fuel limits do **not** bound resulting
text size, copying cost, total memory, or execution time. Repeated unrestricted
doubling can grow rapidly; this is not an embedded/no-heap or predictable-time
string implementation.

## One source decoder

The lexer retains original quoted spelling. Parser.literalValue uses the same
[decoder](../src/Fibril/Source/StringLiteral.idr) for ordinary expression atoms
and console arguments. Supported escapes are quote/backslash and n/r/t; raw
tabs/newlines and unsupported escapes fail. The existing strict UTF-8 loader and
source-wide control/bidi policy remain unchanged.

![String data does not imply an effect](diagrams/strings.svg)

The source syntax requires valid scalar text; direct host construction of
StringValue is raw diagnostic syntax, not a UTF-8/scalar-validity certificate.
Pretty uses escaped host diagnostic rendering, not a promised source serializer.

## Quantities remain explicit

~~~fib
\(1 text : String) => text       -- accepted
\(1 text : String) => "other"    -- rejected: linear input discarded
\(0 text : String) => text       -- rejected at runtime
~~~

A closed literal uses no ambient variables; it cannot silently consume a linear
input. A conditional whose branches use a linear string zero times versus once
still requires unrestricted permission and is rejected. Immutability does not
introduce implicit quantity coercions, dropping, borrowing, or allocation bounds.

## Relationship to console IO

putStrLn is now an ordinary Fibril prelude function over pure String data.
Functions and declarations can pass String values to it, including a value
returned through bind. The core stores pure IO descriptions; only the separate
host runner executes prepared stdout requests. See [IO functions](console-runner.md).
General runtime input, module imports, and a complete effect calculus remain future work.

There is no length/index operation, interpolation, runtime input, native/web
representation, memory-management contract, or string FFI yet.

## Evidence and limits

[Tests.String](../test/src/Tests/String.idr) covers formation/inference, mismatch
payloads, Unicode/escapes, literal conversion, quantity failures, and evaluation.
Scoped and erased typed generators include the String constructors and append
nodes. The closed-String runtime recipe includes concatenation, identity, Unit
cases and Boolean selection, checks the terms, and compares exact literal results.
Tests also cover operand typing, linear-use addition, erased/duplicate rejection,
zero-fuel exhaustion, head forcing, conversion, and decomposed Unicode.

The total host proofs for renaming, basic substitution and composition have new
atomic and binary append cases. Instantiation/root-beta/fuel results continue to
compile against the extended datatype. Concrete binding witnesses include append.
These host syntax proofs and sampled checking properties are not proofs of
ordinary typing preservation, quantitative preservation, language normalization,
erasure correctness, or combined cubical soundness.
