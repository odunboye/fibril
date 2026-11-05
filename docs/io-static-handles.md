# Region-indexed abstract handle typing

Status: abstract source handle type plus a dedicated trusted hosted scope
runner. No source handle creation/file operation or checked native handle
emission exists; the native runtime has a private handle representation.

## Implemented

`Core.Term.FileHandleType region` forms a small type when `region : Type 0`.
The source boundary exposes only the erased type constructor:

```fib
FileHandle : (0 region : Type 0) -> Type 0
```

It has no source value constructor. The hosted runner introduces internal
`FileHandleValue` references only after successful acquisition and rejects such
references in caller entry syntax. Unit cannot be coerced into a handle. Region terms
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

Distinct abstract region parameters are kept distinct. The dedicated hosted
resource runner now introduces per-run internal region identities and maps
scope ownership to host leases, but there is no source scope operation. Users
may write equal concrete region arguments; this type constructor alone does
not establish fresh scope identities. The native runtime now has a private
handle registry, but checked resource emission remains disabled.
Existing console execution is unchanged.

## Next gate

The [inert core scope boundary](io-core-scope.md) now checks a region-polymorphic
callback that returns matching ownership, with nested-region and existential
escape regressions. A [hosted runner](io-resource-execution.md) now introduces
internal handles and checks their ownership return. Hosted
[ownership-returning reads](io-owned-file-reads.md) now advance live generations.
The [native resource runtime](io-native-resources.md) has direct tests; checked
native emission and source exposure remain gated. See
[io-scoped-files.md](io-scoped-files.md) for the proposed protocol and limitations.
