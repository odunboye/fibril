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
