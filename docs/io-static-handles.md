# Region-indexed abstract handle typing

Status: abstract core/source type and typing regressions. No source handle
creation, file operation, generative scope or native handle value is implemented.

## Implemented

`Core.Term.FileHandleType region` forms a small type when `region : Type 0`.
The source boundary exposes only the erased type constructor:

```fib
FileHandle : (0 region : Type 0) -> Type 0
```

It has no value constructor. Unit cannot be coerced into a handle. Region terms
remain relevant to type conversion: handles over distinct abstract region
parameters are not interchangeable. The type former itself is runtime-erased.
Scope transport, renaming/substitution proofs, accounting and normalization
include its region argument; normalization performs no file operations.

Source can define abstract helpers, for example:

```fib
move : (0 region : Type 0) -> (1 handle : FileHandle region) -> FileHandle region
move = \(0 region : Type 0) => \(1 handle : FileHandle region) => handle
```

No source program can obtain a handle from this helper without an input handle.
Quantity-1 input bindings reject discard, duplication, passing captured ownership
to an unrestricted callback and erased extraction. A hypothetical supplied
linear close function can be called once; attempting to use the same handle
again is rejected. Those tests use an abstract function parameter, not an actual
source close primitive.

Fourteen checks cover type formation, unforgeability from Unit, transfer,
returning ownership alongside a result, double-return/escape duplication,
abstract close/use-after-close patterns, capture and cross-region substitution.
Usage-negative source tests first require erased checking success, excluding
syntax/type errors as false evidence of resource rejection.

## What this does not establish

`FileHandle region` is not intrinsically linear independent of its binder.
The future trusted introduction boundary must supply ownership at quantity 1
and preserve that discipline in every operation. A source helper declared with
an unrestricted handle parameter does not magically become linear.

Distinct abstract region parameters are kept distinct, but no fresh generative
region operation exists yet. Users may write equal concrete region arguments;
this type constructor alone does not establish fresh scope identities.

No connection yet exists between these abstract source types and the host-only
`ScopedInput` leases. Nor is there a native handle registry. Existing console
execution and tests remain unchanged.

## Next gate

The [inert core scope boundary](io-core-scope.md) now checks a region-polymorphic
callback that returns matching ownership, with nested-region and existential
escape regressions. It still does not supply real handles or fresh runtime
regions. Next connect the checked protocol to trusted hosted introduction,
cleanup and a matching native registry. See
[io-scoped-files.md](io-scoped-files.md) for the proposed protocol and limitations.
