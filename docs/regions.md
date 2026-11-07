# Scoped regions (`primWithRegion`)

Status: experimental, native C backend only for real reclamation. Source name
`primWithRegion`; core term `WithRegion resultType body`.

```fibril
text : String
text = primWithRegion String (\(0 r : Type 0) => appendString "hello" " region")
```

`body` takes one erased region type. `resultType` is fixed outside the binder, so
it cannot mention `r` and no region-typed value escapes by its type.

## Semantics

- Reference runner / reduction: `WithRegion B body` reduces to `body Unit`. No memory is
  reclaimed; results are identical.
- Native C: everything allocated while the body runs goes into a sub-arena. On exit
  (success or error) the result is deep-copied into the parent arena and the
  sub-arena is freed. Only first-order data can be copied: Unit, Bool, Nat, String,
  Bytes, nominal/variant payloads, pairs, recursive/sequence values. Closures and IO
  descriptions fail with `native region result must be first-order data`.
- A thunk created outside the region but forced inside it is memoized in its own
  owning region, so it stays valid after the region ends.
- The 16 MiB payload cap counts live bytes: a freed region returns its bytes.

## Limits

- The copy-out check is a runtime backstop. The static check (`checkRegionResult`)
  only fires when the result type is concrete at the use site; through the generic
  primitive it usually is not, so function/IO results are rejected at run time.
- No linear capability, `Alloc r A` or borrowing: the region only scopes lifetime.
  Cross-region pointers do not exist; nested regions copy results outward.
- Long tails of Nat/sequence values are copied iteratively; deep non-tail nesting
  is bounded by the runtime depth limit (512).
- Copy-out counts against the step budget.

## Tests

`make region-test` (ASan/UBSan build): a C harness shows 2000 regions of ~200 KiB
succeed while the same allocations without regions exhaust the budget; source tests
check string/Nat results, nesting, memoization after exit, fail-closed function
results and that a region type cannot escape.
