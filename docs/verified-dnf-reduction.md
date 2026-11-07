# Experimental verified DNF reduction

`Fibril.Foundation.DeMorgan.VerifiedReduction` is a separate experimental API;
the checker and existing `normal`, `reduce`, and `canonicalSorted` are unchanged.
`evalVerifiedReduce env ds` proves
`evalDNF env (verifiedReduce ds) = evalDNF env ds` for every signed assignment
and DNF. Positive and negative occurrences are independently assigned: no
Boolean complement law is assumed. The proof composes the existing unconditional
absorption theorem, observation-preserving adjacent deduplication, and a total
structurally recursive insertion sort. Sort observation preservation requires
no comparator laws. Deduplication for an arbitrary `Eq` instance requires the
explicit proof that equality implies equal observations; the DNF instances
provide this proof.

The candidate sorts with `compare`, deduplicates adjacent equal values, then
uses the same `subsetSorted` absorption predicate as `reduce`. Unlike the
production algorithm, its observable list order and hence exact returned normal
form are determined by insertion sort rather than `Data.List.sort`. No specific
difference for the DNF ordering is established, nor is equality with production
`reduce`: the library sort is opaque and no accessible permutation theorem
bridges it to this sort. The theorem establishes semantic equality, not
syntactic equality, sortedness, canonicality, or completeness. In particular,
it does not discharge the conditional soundness theorem for production
reduction. No candidate normalizer is introduced.

The proof-application tests include empty and duplicate inputs, independently
true opposite polarities, and a deliberately unlawful comparator. These proof applications do not establish compatibility with the opaque
library sort.
