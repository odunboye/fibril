# Indexed inductive families

**Implemented checked prototype:** uniform parameters and a separate erased index
telescope, constructor-specific result indices, and index-aware case motives.
This extends [general recursive data](data.md#general-recursive-data). It is a
restricted strictly positive fragment, not a completed inductive-family metatheory.

## Declare a family

```fibril
data Vect (0 A : Type) : (0 length : Nat) -> Type where
  Nil : Vect A Zero
  Cons : (0 n : Nat) -> (value : A) -> (rest : Vect A n) -> Vect A (Succ n)
```

Bind uniform parameters before the colon and indices after it. Every index binder
is explicitly erased and named; finish the single-line header with `-> Type where`.
An index domain may depend on parameters and earlier indices. Constructors repeat
all uniform parameters unchanged, followed by their own result indices. Their
fields may introduce the indices they need: `n` above is an ordinary explicit,
erased constructor argument, not an inferred implicit argument.

`Nil String` has type `Vect String Zero`. `Cons String Zero "first" (Nil String)`
has type `Vect String (Succ Zero)` and cannot be assigned length zero. Header
braces, e.g. `{0 A : Type}`, retain the existing implicit-constructor-parameter
convention; family applications still spell `Vect String n` explicitly.

## Eliminate with an index-aware motive

A motive binds every index erased, in order, then the scrutinee erased. Parameters
stay fixed. For example, an index-preserving copy is:

```fibril
copy : (0 A : Type) -> (0 n : Nat) -> (xs : Vect A n) -> Vect A n
copy A n xs = case xs return (\(0 k : Nat) => \(0 self : Vect A k) => Vect A k) of
  Nil => Nil A
  Cons k value rest => Cons A k value (copy A k rest)
```

The checker types the Nil branch at index `Zero`, and the Cons branch at `Succ k`.
The case result applies the motive to the scrutinee's actual index and value.
It never assumes all constructors have the scrutinee's index. Constructor fields
retain their declared quantities, including erased index fields; attempting to
observe an erased index at runtime is rejected.

For a result independent of the indices, an expected result type supplies a
constant motive automatically. A dependent result currently needs an explicit
`return` motive. Every constructor must be covered, even when a specific index
would make an arm unreachable. There is no index unification, automatic impossible
arm elimination, equality reflection, or general GADT pattern refinement.
Single-constructor cases support explicit motives too.

The [runnable vector example](../examples/modules/indexed-vect/Main.fib) includes
`length`, `copy`, a nonempty-vector `head`, and `append` returning
`Vect A (plus n m)`. Its helper for `head` handles the zero case with `Unit` and
specializes the indexed result at a successor. Index arithmetic uses the existing
Nat recursor: general `Fix` remains opaque to conversion.

```sh
./build/exec/fibril run --source-dir examples/modules/indexed-vect --fuel 4096 examples/modules/indexed-vect/Main.fib
```

It prints `first` followed by `!!!!`, each on its own line. The explicit fuel is
for planning this combined example; evaluation/checking budgets are unchanged.
The native C backend executes the same example and erases index arguments.

## Admission and checks

Families live in `Type 0`. The existing bounds apply: at most four uniform
parameters, four indices, sixteen constructors and eight fields per constructor.
Erased constructor index arguments count as fields. Field types must live in
`Type 0`; uniform parameters and indices are erased. A recursive field must be
the whole family application with its uniform parameters unchanged and exactly
its declared indices. Neither those index expressions nor constructor result
indices may mention the family itself. Recursive occurrences under functions,
nested through another type former, and mutually recursive families are refused.
Generated eliminator helpers are not provided for this slice.

The core stores scoped result indices separately from uniform parameters. It
checks positivity, index arity, the former and every constructor's complete type
before publishing the family. Case checking validates the generic motive and
all constructor branches independently. Existing reduction, usage, termination
and native lowering operate on the same data constructors and cases.

`Tests.IndexedData` covers core admission, wrong-index rejection and dependent
branch types. CLI regressions cover recursive vectors, dependent index telescopes,
implicit constructor parameters, imports, format round trips, linear ownership,
erased-index leakage and nondecreasing recursion. The native suite compares the
vector example with hosted execution. Run `make test` for these and existing
regressions.
