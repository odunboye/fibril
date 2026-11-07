-- Directional literal-universe compatibility, deliberately separate from equality.
-- Scope/obligations: docs/cumulativity-rewriting.md. No cubical subtyping claim.
module Fibril.Core.Compatibility

import Fibril.Core.Term
import Fibril.Core.Reduction

%default total

||| Exhaustion is distinct from an incompatible pair of completed normal forms.
public export
data CompatibilityResult = Compatible | Incompatible | CompatibilityLimit

||| Compare normalized inferred/expected types directionally.
||| Universe i is acceptable at Universe j when i <= j. All other pairs require
||| structural beta-normal-form equality; no Pi covariance or quantity coercion.
||| Callers must separately establish type formation. This is not conversion.
public export
compatibleTypes : Nat -> Term n -> Term n -> CompatibilityResult
compatibleTypes fuel inferred expected =
  case (normalize fuel inferred, normalize fuel expected) of
    (Normal (Universe i), Normal (Universe j)) =>
      if i <= j then Compatible else Incompatible
    (Normal actual, Normal wanted) =>
      if sameSyntax actual wanted then Compatible else Incompatible
    _ => CompatibilityLimit

||| As above, but transparent globals unfold within the same conversion fuel.
public export
compatibleTypesGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Term n -> Term n -> CompatibilityResult
compatibleTypesGlobals globals fuel inferred expected =
  case (normalizeGlobals globals fuel inferred, normalizeGlobals globals fuel expected) of
    (Normal (Universe i), Normal (Universe j)) =>
      if i <= j then Compatible else Incompatible
    (Normal actual, Normal wanted) =>
      if sameSyntax actual wanted then Compatible else Incompatible
    _ => CompatibilityLimit
