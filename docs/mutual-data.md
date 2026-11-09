# Mutually recursive data

Status: implemented checked prototype for groups of two to eight families sharing
one erased parameter telescope. Every recursive occurrence must be a whole member
family applied to the unchanged parameters. Indexed mutual families and nested
occurrences through other type constructors remain outside this slice.

```fibril
mutual where
  data Even : Type where
    ZeroEven : Even
    NextEven : (odd : Odd) -> Even
  data Odd : Type where
    NextOdd : (even : Even) -> Odd
```

Each data header and its constructors are aligned inside the group. Compact data
alternatives retain their existing syntax. Constructor names share the module's
ordinary namespace and must be distinct. An `export` marker before `mutual where`
exports the entire bundle, including its types and constructors.

Parameters may have different names in different families, but their scoped types
and quantities must describe the same telescope. They are explicitly erased.
A recursive field can name any member, using the current family's parameters in
order. Fields may retain their existing erased, linear or unrestricted quantities.
Families live in `Type 0`; field types, constructor counts, field counts, source
construction and checking budgets retain the existing admission bounds.

## Check a group atomically

The module driver first elaborates parameter telescopes against previously checked
definitions. It then makes all group formers provisionally visible to elaborate
constructor fields. No family is published at that point. The core verifies:

- fresh, distinct keys and a compatible common parameter telescope;
- absence of group references in parameter domains;
- positivity across every group member, including negative references to partners;
- every former and every constructor's complete type under the simultaneous context.

Only a successful check returns the extended runtime context. A bad partner cannot
leave a half-admitted group. Forward data declarations outside a mutual block are
still refused. Generated eliminator helpers are not provided for these groups.

## Structural computation

A whole checked data-family field is a proper component of the value being matched.
The size-change extractor can follow that relation across partner-family cases:

```fibril
render : (value : Even) -> String
render value = case value of
  ZeroEven => "0"
  NextEven odd => case odd of
    NextOdd even => appendString "." (render even)
```

The recursive argument is a component reached through two constructors. Calling
`render` on the original value or a reconstructed wrapper is refused. The body
must still pass independent type and usage checking. This adds data groups; the
existing restrictions on heterogeneous mutual *function* groups still apply.

The [example](../examples/modules/mutual-data/Main.fib) prints `..0`:

```sh
./build/exec/fibril run --source-dir examples/modules/mutual-data examples/modules/mutual-data/Main.fib
```

The hosted and native C backends use the existing data constructors and cases;
there is no new runtime value representation. Checked imports, qualified names,
source references, symbols and formatting include group members.

`Tests.MutualData` checks atomic admission, malformed partners, duplicate keys,
parameter cycles and incompatible kinds. CLI tests cover positive Even/Odd and
parameterized Tree/Forest groups, imports, format round trips, group bounds,
negative recursion and nondecreasing/rebuilt calls. `make test` includes these
checks and native agreement.
