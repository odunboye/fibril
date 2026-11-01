# Pure String values

Status: implemented primitive String typing and opaque literal data in the ordinary
core. This is not a string library, backend ABI, or general IO/effect system.

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
requires a separate main : IO Unit console entry.

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

Console arguments now use ordinary expression parsing and a separate pure
planning stage. Closed String expressions, including local let/lambda bindings
and applications, can be checked/reduced before becoming PrintLine requests.
Its action data still does not contain a core IO term. File-level helpers,
shared bindings between actions, and general effect composition remain future
work; see [console arguments](console-runner.md#compute-a-string-argument).

There is no concatenation, length/index operation, interpolation, runtime input,
native/web representation, memory-management contract, or string FFI yet.

## Evidence and limits

[Tests.String](../test/src/Tests/String.idr) covers formation/inference, mismatch
payloads, Unicode/escapes, literal conversion, quantity failures, and evaluation.
Scoped and erased typed generators include both constructors. A new runtime
property constructs closed String programs using identity, Unit cases and Boolean
selection, checks them, and verifies their literal normal forms.

The total host proofs for renaming, basic substitution and composition have new
atomic cases. Instantiation/root-beta/fuel results continue to compile against
the extended datatype. Concrete binding witnesses also include String atoms.
These host syntax proofs and sampled checking properties are not proofs of
ordinary typing preservation, quantitative preservation, language normalization,
erasure correctness, or combined cubical soundness.
