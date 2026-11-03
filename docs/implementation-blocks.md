# Named method-body implementation blocks

## Use cases

Use a method block when constructing an implementation with several operations: named assignments make omissions and misspellings visible and avoid remembering constructor field order. A text Monoid can assign `merge = appendString` and `identity = ""`.

Prefer the explicit dictionary constructor expression when targeting an alias/plain record, when the interface schema is unavailable, or when the constructor application is already clearer. This is construction convenience, not a new checking rule.

**Implemented prototype:** an explicitly typed implementation can supply named
method values instead of writing its dictionary constructor application:

~~~fibril
implementation textMonoid : Algebra.Monoid String where
  merge = appendString
  identity = ""
~~~

This is declaration elaboration, not instance search or a new core rule.
The earlier explicit dictionary expression form remains supported.

![Method block lowering](diagrams/implementation-blocks.svg)

## Visible schemas and ordering

A block's final result must directly name an available interface, with all
interface parameters explicit. [Parameterized factories](implementation-factories.md)
may precede that result with erased parameters and dictionary parameters; those
header binders scope over the method bodies. Indented header continuations are
accepted, with where ending its line. Earlier local interfaces, including private ones, are
available. In project checking, exported interfaces from **checked direct
dependencies** supply qualified schemas. Transitive reachability alone does not
grant access, and private interface metadata is not published.

The schema contains only the constructor name, parameter count and ordered
method names. It supplies field ordering, not trusted term types or a checking
certificate. The body values go through ordinary constructor application
checking, so method types and argument quantities are independently enforced.

Method assignments may occur in any source order. The elaborator rejects:

- Missing, duplicate or unknown method names.
- Unavailable schemas or omitted interface arguments.
- Wrong method values, quantities or unresolved ordinary references.

A block targeting a type alias or plain record is not guessed into an
interface. Use the existing explicit dictionary expression when a visible
interface schema is unavailable. Qualified own-module names are accepted;
forward references to later interface declarations are not.

## Method expressions and scope

Methods use name = expression. Multiline expressions continue at a deeper
indent than the method headers:

~~~fibril
implementation strings : Combine String where
  combine = \(1 left : String) => \(1 right : String) =>
    appendString left right
~~~

Method name and = share a header line. Headers align; the next header at that
indent ends the previous body. Expression parsing, typed binders and flat do
statement restrictions otherwise remain unchanged.

Method bodies use the ordinary surrounding environment. They are not recursive
bindings, and one method assignment does not create a local name visible in
another body. Factor shared code into ordinary earlier helpers. Named method
arguments/pattern clauses, inferred lambda binders, defaults, inheritance and
automatic dictionary selection are not added.

Formatting uses the existing guarded expression layout with method-relative
continuation indentation. It can wrap long bodies without saving files or
changing the authored block shape. Interface/implementation where headers still
remain single-line framing syntax.

## Checking, publication and resources

The parser retains ImplementationBlock with its actual header and method tokens.
It does not generate constructors or look up interfaces.
[Elaboration.Interface](../src/Fibril/Elaboration/Interface.idr) holds layout
metadata; [Elaboration.Declaration](../src/Fibril/Elaboration/Declaration.idr)
owns schema-guided ordering and ordinary dictionary-expression generation.

Generated constructor references carry the implementation origin, not a forged
authored constructor token. Syntax-only navigation walks the actual target and
body references. Only the named dictionary is a top-level binding; method
assignment headers do not pretend to be new global definitions.

The driver publishes imported schemas only after the entire dependency module
checks, including private and unused definitions. Generated implementations
pass normal resolution, expanded-core admission, erased/runtime checking and
the existing structural dictionary-shape gate before exports or IO planning.

One block consumes one declaration slot, not one per assigned method.
Generated expression size is admitted cumulatively before construction. Source,
parser, graph, node and checker budgets remain independent; these are not
allocation/time guarantees. No unchecked generated definition or law certificate
is installed.

Schemas are ordinary public API data, not proof objects. The source pipeline
derives them from authored interfaces; a caller forging metadata does not obtain
a typing or nominal-membership certificate.

## Inspection and examples

elaborate PATH remains local and explicitly unchecked. It can lower local
interface blocks, but does not load imports to discover their schemas. An
imported block therefore reports schema unavailable in this single-file command;
project check/run supplies the checked dependency schemas. Syntax-only
formatting and symbols can still inspect such a file.

~~~sh
./build/exec/fibril run --source-dir examples/modules/interface-blocks examples/modules/interface-blocks/Main.fib
~~~

[The example graph](../examples/modules/interface-blocks/Main.fib) runs the same
generic String/Bool operations and Monoid shape as the explicit-dictionary
example. [Text implementations](../examples/modules/interface-blocks/Instances/Text.fib)
use blocks, with identity intentionally preceding merge to exercise reordering.
The Boolean implementation retains the explicit constructor form. Output:

~~~text
Hello, interfaces!
Explicit dictionaries!
Monoid shape!
~~~

Tests cover local/imported/qualified schemas, ordering, errors, multiline bodies,
guarded formatting, declaration/construction quotas, private/transitive visibility
and rejection of unused invalid dependencies before schema publication. [Named constraints/local selection](constraints.md) now use these dictionaries.
Algebraic laws, coherent global instance lookup and operators remain separate work.
