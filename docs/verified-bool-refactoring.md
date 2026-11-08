# Verified Boolean refactoring: semantic agreement, not cubical paths

Status: design approved by supervisor for implementation on `feature/cubical-refactoring` at `7169ce6`; no master integration. Common Path v0 is unchanged.

## Decision and exact syntax

Add the standalone ordinary-source metadata rule:

```fib
allow : (1 enabled : Bool) -> Bool
allow enabled = enabled
reviewed : (1 enabled : Bool) -> Bool
reviewed enabled = if enabled then True else False
cubical policyStable : allow = reviewed by boolCases
requires policyStable
main : IO Unit
main = putStrLn (if allow True then "feature enabled" else "feature disabled")
```

`by boolCases` certifies **semantic pointwise Boolean agreement**, not source equality, `CommonFaceEqual`, `CommonShadowPath`, or path existence. `by refl` continues to mean the existing syntactically identical constant-path guard. Checking reports and documentation must distinguish these meanings. The metadata label remains erased and is never usable as an ordinary term, cast, conversion equation, or path hypothesis. Existing declaration ordering, actual-consumer reference, standalone-only, formatting, and tooling restrictions apply unchanged.

The exact additional fragment is a closed unary lambda of type `Arrow q BoolTy BoolTy`, with the same `q` at both endpoints, `q` Linear or Unrestricted. Its literal intrinsic body grammar is:

```text
body = Ref Here | Boolean b | If body body body
```

Both endpoints must pass the existing independently elaborated `PureImage`, exact type/value re-embedding, actual `DefinitionAt` contextual alignment, `inferRuntime`, and `Uses` gates. Fragment recognition is exact, with no wrapper stripping or normalization to gain admission. Applications (even identity beta wrappers), Unit elimination, higher-order bodies/types, dependent types, erased binders, globals/Prelude dependencies, recursion, effects and resources are rejected for `boolCases`. They do not acquire proof authority through erasure.

## Machine proof obligations

Implement in a separate total module; do not add frozen calculus constructors.

1. Recognize the body grammar with an actual equality from its intrinsic embedding to the supplied `Q.Term [BoolTy] BoolTy`. Retain the original `PureImage` annotations and exact production source. Prove reconstructed body/core lambda equals `coreTerm` with those actual annotations.
2. Define a structurally recursive evaluator over the entire supported body grammar, including arbitrary nested conditionals. No fuelled production-normalizer result, runtime samples, trusted Boolean claim, assertion, postulate, or assumed endpoint path may replace a proof.
3. Define reduction traces whose individual contractions carry equality to the actual `Core.Reduction.step`. Prove Boolean condition contraction/congruence, closed substitution of the input, root beta, and total reduction of the exact lambda applied to either constructor to its evaluator result. Prove that result is a core normal form. This is an operational theorem for the exact restricted core trees, not whole-production operational adequacy or native compiler correctness.
4. A checked certificate contains constructive equalities `eval left False = eval right False` and `eval left True = eval right True`. A total theorem eliminates an arbitrary `b : Bool` to establish `(b : Bool) -> eval left b = eval right b`, and combines the two operational reductions to a common Boolean normal form for every input. Unequal constructor results reject with a constructor-specific diagnostic. Exhaustion is not inequality.
5. If exposing the selected higher-order setoid relation, construct canonical `HigherOrderTerm` witnesses for the exact embedded syntax/typing and prove their semantics equal this evaluator. Then derive `(x,y : Bool) -> x = y -> apply f x = apply g y` by Bool elimination. No `HigherOrderAlignment` may be fabricated between different syntax, and erasure alone cannot establish witness coherence. The operational all-input theorem is the required milestone; the supervisor permits deferring this additional semantic bridge only if explicitly documented, rather than claiming it was proved.
6. Retain independently constructed `Uses` for each actual endpoint. Semantic agreement does not identify quantities or transfer permissions. Linear duplication/discard remain rejected as the quantitative judgment dictates; Unrestricted duplication/discard remain supported if otherwise valid.

## Cubical significance and limits

The existing grammar has no Boolean computation equation, lambda equality, function extensionality, or equality reflection. Consequently neither a constant function body nor a structural Bool eliminator supplies the missing face-restricted equalities between these two different lambda trees. Building a `CommonAbstract` would simply move the unproved boundary obligation; an assumed named path would assert the goal. Do not manufacture either.

This milestone establishes a useful verified-refactoring prerequisite in the semantic model/operational fragment. It is not an actual cubical programming feature. A future actual path milestone needs a separate approved extension (Bool computation, suitable lambda/extensional equality and their substitution/dimension/boundary soundness), followed by real abstraction admission. No composition, filling, transport, general conversion, runtime path, or source-equality reflection is selected here.

## Costs and failure behavior

Keep existing source/parser/elaboration limits and extraction depth 64. Add a shared 1024-node body-recognition allowance across both endpoints; each variable, literal, or conditional counts one, siblings receive remaining fuel. Unsupported syntax and exhaustion fail closed. Two constructor evaluations per endpoint terminate structurally and visit at most its body nodes per evaluation. Evidence comparison is constructive Boolean equality, not a solver. Reduction proof generation is structural and may traverse/compose traces repeatedly (conservatively quadratic in body size); no combined time/allocation theorem is claimed. Existing production elaboration/checking and caller allocation are outside this local accounting. Do not reset a shared cap per branch or silently invoke uncapped reduction.

## Acceptance tests and execution gates

- Machine-level generic theorem checks for all inputs; identity versus conditional are genuinely different core trees. Cover both Bool constructors, nested conditionals, exact re-embedding, and same-quantity requirements.
- Reject changing the False output and changing the True output independently; wrong type, non-unary functions, applications, recursion, globals, effects/resources, erased/dependent types, quantity mismatch, linear discard/duplication, and shared node/depth exhaustion. Include diagnostic-specific negative Idris fixtures for changed certificate indices/results and prohibit deriving frozen cubical equality from a semantic certificate.
- CLI: ordinary `check`, `check --erased`, `check --json`, `eval`, `run`, `emit-c`, `emit-c-binary`, and `emit-c-interactive` all traverse the same gate before execution/emission. Positive supported native run uses strict C flags. Check differing constructor behavior explicitly in hosted/native consumer examples.
- Identical emitted C and evaluation reports with/without valid metadata establish proof erasure observationally. Runtime calls the actual left definition, never a truth table substituted by the checker. Check reporting may include explicit semantic-agreement text; evaluation/runtime reports stay unchanged.
- Keep ordinary `by refl` tests unchanged (in particular it must still reject identity-vs-conditional), metadata name/order/shadowing/consumer/format rules, standalone project/import/package/tooling exclusions, and ordinary files without metadata.
- Sequential validation: `make -j8 build`; `bash tools/test_cubical_worktree.sh`; `python3 tools/test_cubical_frontend.py`; `python3 tools/test_cubical_application.py`; broader `make test` and `make io-test` as available, with private TTC staging and no shared-cache installation.

## Architecture and integration plan

Starting seams: `Cubical.Source.PureDefinition`, `Cubical.Source.Application.checkConstantPaths`, `Source.Declaration.parseOne`, declaration metadata and `Source.Shape`, `Driver.Check.prepareSource`/checking report, and `tools/test_cubical_application.py`. Add a dedicated `Cubical.Source.BoolCases` module and source-named test module rather than expanding `CommonAdmission` or production reduction. Represent metadata certificate kind explicitly; preserve the actual endpoint/location evidence in a sum of constant-path and semantic-agreement evidence.

Master is `43f7d56`, with unrelated recursive-data/multi-field work and other active worktrees. Do not merge, rebase, stage, commit, install shared packages, or modify another worktree. A later integration gate requires separate permission, a clean-worktree check, and inspection of conflicts in source declaration/parser/elaboration/core files; new constructors must remain rejected by exact fragment recognition. No master integration is required for this milestone.
