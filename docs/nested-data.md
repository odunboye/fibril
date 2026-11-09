# Nested recursive data through fixed lists

General data may contain recursive occurrences beneath the intrinsic fixed-list
container. The core checks strict positivity through `SeqType`; it does not infer
variance for arbitrary user-defined containers.

```fibril
data Items (0 A : Type) : Type where
  eliminator foldItems
  Nil : Items A
  Cons : (1 head : A) -> (1 tail : Items A) -> Items A

data Rose : Type where
  Node : (1 children : Items Rose) -> Rose
```

The [runnable example](../examples/modules/nested-data/Main.fib) computes a
Rose tree's size by calling itself on each child in `foldItems`. Hosted execution
and native C emission use the existing sequence and data representations.

## Admission and structural recursion

A recursive field may contain one or more intrinsic fixed-sequence layers.
At the innermost recursive family application, uniform parameters must remain
unchanged and in order, and indices obey the existing indexed-data rules.
The positivity traversal has a budget of 64 steps. Function-space occurrences,
unknown containers and nonuniform recursive parameters are rejected.

A data field containing a sequence is a proper component of its constructor.
Sequence cases and folds expose their actual head and tail as further components.
Only heads with a checked data-family or sequence type receive this evidence.
A fold's computed result receives no decrease evidence. Recursive calls on
rebuilt nodes, the original root, or computed fold results remain rejected.

Elaboration exposes the generated fixed-list fold through an exact checked eta
helper view. It preserves all arguments, including erased type arguments, for
logical termination checking. It does not unfold arbitrary user functions or
normalize recursive bodies. Ordinary core type, quantity and size-change checks
still validate the resulting term. The fold callback remains unrestricted, so it
cannot capture ambient linear values; its head and computed result remain linear.

This supports fixed-list nesting. It does not implement arbitrary container
variance, nested function spaces, or polymorphic recursion. See [source data](data.md)
and [indexed families](indexed-data.md) for the other admission limits.
