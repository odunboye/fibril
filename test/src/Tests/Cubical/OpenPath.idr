module Tests.Cubical.OpenPath

import Data.Fin
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

p : NeutralPath 2
p = PathBetween FZ (FS FZ)

accepted : Result -> Bool
accepted Accepted = True
accepted _ = False

exhausted : Result -> Bool
exhausted Exhausted = True
exhausted _ = False

rejected : Result -> Bool
rejected Rejected = True
rejected _ = False

export
checks : List (String, Bool)
checks =
  [ ("open neutral path abstraction", accepted (checkAbstraction {n=0} 12 p (At (Var FZ)) FZ (FS FZ)))
  , ("open neutral path reversal", accepted (checkAbstraction {n=0} 12 p (At (Reverse (Var FZ))) (FS FZ) FZ))
  , ("open path rejects wrong boundary", not (accepted (checkAbstraction {n=0} 12 p (At (Var FZ)) (FS FZ) FZ)))
  , ("square meet is left endpoint on either zero face",
      accepted (convertToVariable {n=2} 12 (Under (SEndpoint FZ False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) FZ) &&
      accepted (convertToVariable {n=2} 12 (Under (SEndpoint (FS FZ) False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) FZ))
  , ("square meet one faces are neutral boundaries",
      accepted (convertNeutrals {n=2} 12 (Under (SEndpoint FZ True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Var (FS FZ))) &&
      accepted (convertNeutrals {n=2} 12 (Under (SEndpoint (FS FZ) True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Var FZ)))
  , ("square one face mismatch and exhaustion differ",
      rejected (convertNeutrals {n=2} 12 (Under (SEndpoint FZ True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Reverse (Var (FS FZ)))) &&
      exhausted (convertNeutrals {n=2} 4 (Under (SEndpoint FZ True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Var (FS FZ))))
  , ("zero faces mismatch and exhaustion differ",
      rejected (convertToVariable {n=2} 12 (Under (SEndpoint FZ False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) (FS FZ)) &&
      exhausted (convertToVariable {n=2} 3 (Under (SEndpoint FZ False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) FZ))
  , ("neutral equality uses De Morgan algebra not Boolean vertices",
      rejected (convertNeutrals {n=1} 12 unrestricted p
        (Meet (Var FZ) (Reverse (Var FZ))) Zero) &&
      accepted (convertNeutrals {n=1} 12 unrestricted p
        (Reverse (Meet (Var FZ) (Reverse (Var FZ))))
        (Join (Reverse (Var FZ)) (Var FZ))))
  , ("restricted disjunction validates non-Boolean identity only on boundary",
      accepted (convertNeutrals {n=1} 12
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))) p
        (Meet (Var FZ) (Reverse (Var FZ))) Zero) &&
      rejected (convertNeutrals {n=1} 12 unrestricted p
        (Join (Var FZ) (Reverse (Var FZ))) One))
  , ("restriction substitution preserves a restricted neutral equality",
      accepted (convertNeutrals {n=1} 12
        (substituteRestriction (\_ => Reverse (Var FZ)) (the (Restriction 1) (Under (SEndpoint FZ True)))) p
        (substituteScoped (\_ => Reverse (Var FZ)) (the (ScopedInterval 1) (Var FZ))) One))
  , ("other zero face mismatch and exhaustion differ",
      rejected (convertToVariable {n=2} 12 (Under (SEndpoint (FS FZ) False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) (FS FZ)) &&
      exhausted (convertToVariable {n=2} 3 (Under (SEndpoint (FS FZ) False)) p
        (At (Meet (Var FZ) (Var (FS FZ)))) FZ))
  , ("other one face mismatch and exhaustion differ",
      rejected (convertNeutrals {n=2} 12 (Under (SEndpoint (FS FZ) True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Reverse (Var FZ))) &&
      exhausted (convertNeutrals {n=2} 4 (Under (SEndpoint (FS FZ) True)) p
        (Meet (Var FZ) (Var (FS FZ))) (Var FZ)))
  , ("neutral equality false face and endpoint declarations",
      accepted (convertNeutrals {n=1} 12 (Under SBottom) p Zero One) &&
      rejected (convertNeutrals {n=1} 12 unrestricted p Zero One) &&
      accepted (convertNeutrals {n=1} 12 unrestricted
        (the (NeutralPath 2) (PathBetween FZ FZ)) Zero One))
  , ("neutral equality fixed cap applies even to reflexivity",
      exhausted (convertNeutrals {n=1} 100 unrestricted p
        (Meet (Meet (Var FZ) (Var FZ)) (Meet (Var FZ) (Var FZ)))
        (Meet (Meet (Var FZ) (Var FZ)) (Meet (Var FZ) (Var FZ)))))
  , ("dimension substitution identity and composition",
      let t : OpenTerm 2 1 = At (Var FZ)
          once : OpenTerm 2 1 = mapDimensions (\_ => Meet (Var FZ) One) t
          twice : OpenTerm 2 1 = mapDimensions (\_ => Reverse (Var FZ)) once
          composed : OpenTerm 2 1 = mapDimensions (\_ => Meet (Reverse (Var FZ)) One) t
       in case (mapDimensions Var t, t, twice, composed) of
            (At a, At b, At c, At d) =>
              accepted (convertNeutrals {n=1} 12 unrestricted p a b) &&
              accepted (convertNeutrals {n=1} 12 unrestricted p c d)
            _ => False)
  , ("square meet is right endpoint on both one faces",
      accepted (convertToVariable {n=2} 12 (Under (SConjunction (SEndpoint FZ True) (SEndpoint (FS FZ) True))) p
        (At (Meet (Var FZ) (Var (FS FZ)))) (FS FZ)))
  , ("meet with reverse is not zero", not (accepted (convertToVariable {n=2} 12 unrestricted p
        (At (Meet (Var FZ) (Reverse (Var FZ)))) FZ)))
  , ("coincident endpoints convert under their disjunction",
      accepted (convertToVariable {n=1} 12
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)))
        (the (NeutralPath 2) (PathBetween FZ FZ)) (At (Var FZ)) FZ))
  , ("distinct endpoints do not convert under their disjunction",
      not (accepted (convertToVariable {n=1} 12
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))) p (At (Var FZ)) FZ)) &&
      not (accepted (convertToVariable {n=1} 12
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))) p (At (Var FZ)) (FS FZ))))
  , ("no matching endpoint converts only on the empty face",
      accepted (convertToVariable {n=1} 12 (Under SBottom)
        (the (NeutralPath 3) (PathBetween FZ (FS FZ))) (At (Var FZ)) (FS (FS FZ))) &&
      not (accepted (convertToVariable {n=1} 12 unrestricted
        (the (NeutralPath 3) (PathBetween FZ (FS FZ))) (At (Var FZ)) (FS (FS FZ)))))
  , ("coincident endpoint conversion respects node budget",
      exhausted (convertToVariable {n=1} 3
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)))
        (the (NeutralPath 2) (PathBetween FZ FZ)) (At (Var FZ)) FZ) &&
      accepted (convertToVariable {n=1} 4
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)))
        (the (NeutralPath 2) (PathBetween FZ FZ)) (At (Var FZ)) FZ))
  , ("endpoint disjunction is not top", not (accepted (convertToVariable {n=2} 12
        (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))) p (AVar FZ) (FS FZ))))
  , ("dimension substitution preserves endpoint computation",
      accepted (convertToVariable {n=2} 12 unrestricted p
        (mapDimensions (\_ => Zero) (the (OpenTerm 2 1) (At (Var FZ)))) FZ))
  , ("term renaming preserves neutral path endpoints",
      accepted (convertToVariable {n=2} 12 unrestricted
        (renamePath FS p) (renameTerms FS (the (OpenTerm 2 2) (At Zero))) (FS FZ)))
  , ("open conversion fails closed on exhaustion", exhausted (convertToVariable {n=2} 0 unrestricted p (AVar FZ) FZ))
  , ("open conversion refuses unsupported neutral equality", not (accepted (convertToVariable {n=2} 12 unrestricted p (At (Var FZ)) FZ)))
  ]
