module Tests.Cubical.OpenPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Square
import Fibril.Cubical.Logical.ReusablePath
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

p : NeutralPath 2
p = PathBetween FZ (FS FZ)

paths : PathContext 2 2
paths = [p, p]

reversals : Nat -> ScopedInterval n -> ScopedInterval n
reversals Z r = r
reversals (S count) r = Reverse (reversals count r)

accepted : Result -> Bool
accepted Accepted = True
accepted _ = False

exhausted : Result -> Bool
exhausted Exhausted = True
exhausted _ = False

rejected : Result -> Bool
rejected Rejected = True
rejected _ = False

-- Structural comparison keeps these examples sensitive to the exact substitution,
-- rather than merely conversion on an empty face.
sameInterval : ScopedInterval n -> ScopedInterval n -> Bool
sameInterval Zero Zero = True
sameInterval One One = True
sameInterval (Var x) (Var y) = x == y
sameInterval (Reverse x) (Reverse y) = sameInterval x y
sameInterval (Meet x y) (Meet a b) = sameInterval x a && sameInterval y b
sameInterval (Join x y) (Join a b) = sameInterval x a && sameInterval y b
sameInterval _ _ = False

sameContextTerm : ContextTerm m k n -> ContextTerm m k n -> Bool
sameContextTerm (Variable x) (Variable y) = x == y
sameContextTerm (ApplyPath p r) (ApplyPath q s) = p == q && sameInterval r s
sameContextTerm _ _ = False

branching : Nat -> ScopedInterval n -> ScopedInterval n
branching Z x = x
branching (S n) x = let y = branching n x in Meet y y

-- Compare the preflight with an independently constructed reference for small inputs.
preflightReference : Nat -> ScopedInterval 1 -> ScopedInterval 2 -> Bool
preflightReference fuel replacement input =
  let env : Vect 1 (ScopedInterval 1) = [replacement]
      body : ContextTerm 2 2 2 = ApplyPath FZ input
      output = substituteScoped (liftContextDimensions (\i => index i env)) input
      reference = case fuel of
        Z => False
        S f => case intervalNodes f replacement of
          Nothing => False
          Just Z => False
          Just (S remaining) => isJust (intervalNodes (min 9 remaining) output) in
  boundedSubstitutionPreflight fuel env body == reference

-- Compare each returned path face against the corresponding instantiated edge.
asymmetricCtx : Telescope 2 1
asymmetricCtx = Extend Empty (Tvar FZ) (Tvar (FS FZ))

checkFixedI : (ctx : Telescope 2 1) ->
              CheckedPath {n=1} ctx (Tapp FZ (Var (FS FZ)))
                (Tapp FZ (Var FZ)) (Tapp FZ (Var FZ)) -> Bool
checkFixedI ctx p = case (applyPath 12 p Zero, applyPath 12 p One) of
  (Right l, Right r) =>
    accepted (Telescope.convertRestricted 12 unrestricted ctx l (Tapp FZ (Var FZ))) &&
    accepted (Telescope.convertRestricted 12 unrestricted ctx r (Tapp FZ (Var FZ))) &&
    case (l, r) of
      (Tapp FZ (Var FZ), Tapp FZ (Var FZ)) => True
      _ => False
  _ => False

checkFixedJ : (ctx : Telescope 2 1) ->
              CheckedPath {n=1} ctx (Tapp FZ (Var FZ))
                (Tvar FZ) (Tvar (FS FZ)) -> Bool
checkFixedJ ctx p = case (applyPath 12 p Zero, applyPath 12 p One) of
  (Right l, Right r) =>
    accepted (Telescope.convertRestricted 12 unrestricted ctx l (Tvar FZ)) &&
    accepted (Telescope.convertRestricted 12 unrestricted ctx r (Tvar (FS FZ))) &&
    case (l, r) of
      (Tapp FZ Zero, Tapp FZ One) => True
      _ => False
  _ => False

export
checks : List (String, Bool)
checks =
  [ ("asymmetric square application selects and rechecks both pairs of edges",
      case checkBoundSquare {n=1} 16 asymmetricCtx
             (Tapp FZ (Var (FS FZ))) (Tvar FZ) (Tvar (FS FZ))
             (Tapp FZ (Var FZ)) (Tapp FZ (Var FZ)) of
        Left _ => False
        Right sq => case (applySquare 32 FixI sq (Var FZ), applySquare 32 FixJ sq (Var FZ)) of
          (Right pi, Right pj) => checkFixedI asymmetricCtx pi && checkFixedJ asymmetricCtx pj
          _ => False)
  , ("square application reaches and exhausts independent path recheck",
      let body : Term 2 1 2 = Tapp FZ (Var (FS FZ))
          edge : Term 2 1 1 = Tapp FZ (Var FZ)
          left : Term 2 1 1 = Tvar FZ
          right : Term 2 1 1 = Tvar (FS FZ)
          r : ScopedInterval 0 = reversals 3 Zero in
      case checkBoundSquare 16 asymmetricCtx body left right edge edge of
        Left _ => False
        Right sq => case (applySquare 32 FixI sq r,
                          checkPath 32 asymmetricCtx (Tapp FZ (reversals 3 Zero)) (Tapp FZ r) (Tapp FZ r)) of
          (Left Exhausted, Left Exhausted) => True
          _ => False)
  , ("square application rechecks both directions and beta",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          body : Term 2 1 3 = Tapp FZ (Meet (Var FZ) (Var (FS FZ)))
          edge : Term 2 1 2 = Tapp FZ (Var FZ)
          zero : Term 2 1 2 = Tvar FZ in
      case checkBoundSquare 16 ctx body zero edge zero edge of
        Left _ => False
        Right sq => case (applySquare 32 FixI sq (Var FZ), applySquare 32 FixJ sq (Var FZ),
                          applySquare 32 FixI sq Zero, applySquare 32 FixJ sq One) of
          (Right pi, Right pj, Right _, Right _) =>
            case (applyPath 12 pi One, applyPath 12 pj One) of
              (Right (Tapp FZ (Meet One (Var FZ))),
               Right (Tapp FZ (Meet (Var FZ) One))) => True
              _ => False
          _ => False)
  , ("square application preserves ambient scope and bounds",
      let ctx : Telescope 1 1 = Extend Empty (Tvar FZ) (Tvar FZ)
          body : Term 1 1 3 = Tapp FZ (Var (FS (FS FZ)))
          edge : Term 1 1 2 = Tapp FZ (Var (FS FZ)) in
      case checkBoundSquare 16 ctx body edge edge edge edge of
        Left _ => False
        Right sq => case (applySquare 32 FixI sq (Reverse (Var FZ)),
                          applySquare 0 FixJ sq Zero) of
          (Right p, Left Exhausted) => case applyPath 12 p One of
            Right (Tapp FZ (Var FZ)) => True
            _ => False
          _ => False)
  , ("square application rejects amplified output with admitted input",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          body : Term 2 1 2 = Tapp FZ (Meet (Var FZ) (Var (FS FZ)))
          edge : Term 2 1 1 = Tapp FZ (Var FZ)
          zero : Term 2 1 1 = Tvar FZ in
      case checkBoundSquare 16 ctx body zero edge zero edge of
        Left _ => False
        Right sq => case applySquare 32 FixI sq (reversals 12 Zero) of
          Left Exhausted => True
          _ => False)
  , ("square application counts expanded output before substitution",
      let ctx : Telescope 1 0 = Empty
          body : Term 1 0 2 = Tvar FZ
          edge : Term 1 0 1 = Tvar FZ in
      case checkBoundSquare 16 ctx body edge edge edge edge of
        Left _ => False
        Right sq => case applySquare 32 FixI sq (reversals 32 Zero) of
          Left Exhausted => True
          _ => False)
  , ("checked square has four genuine edges",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          body : Term 2 1 2 = Tapp FZ (Meet (Var FZ) (Var (FS FZ)))
          edge : Term 2 1 1 = Tapp FZ (Var FZ)
          zero : Term 2 1 1 = Tvar FZ
          wrong : Term 2 1 1 = Tvar (FS FZ) in
      accepted (checkSquare 13 ctx body zero edge zero edge) &&
      exhausted (checkSquare 12 ctx body zero edge zero edge) &&
      rejected (checkSquare 16 ctx body wrong edge zero edge) &&
      rejected (checkSquare 16 ctx body zero wrong zero edge) &&
      rejected (checkSquare 16 ctx body zero edge wrong edge) &&
      rejected (checkSquare 16 ctx body zero edge zero wrong) &&
      exhausted (checkSquare 2 ctx body zero edge zero edge) &&
      case checkBoundSquare 16 ctx body zero edge zero edge of
        Right _ => True
        Left _ => False)
  , ("square edges retain ambient dimensions under both binders",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          body : Term 2 1 3 = Tapp FZ (Var (FS (FS FZ)))
          edge : Term 2 1 2 = Tapp FZ (Var (FS FZ))
          captured : Term 2 1 2 = Tapp FZ (Var FZ) in
      accepted (checkSquare 16 ctx body edge edge edge edge) &&
      rejected (checkSquare 16 ctx body captured edge edge edge) &&
      rejected (checkSquare 16 ctx body edge edge captured edge))
  , ("square admission shares its budget across every input",
      let ctx : Telescope 1 0 = Empty
          body : Term 1 0 2 = Tvar FZ
          edge : Term 1 0 1 = Tvar FZ in
      exhausted (checkSquare 4 ctx body edge edge edge edge) &&
      accepted (checkSquare 5 ctx body edge edge edge edge))
  , ("asymmetric square distinguishes i and j edges",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          body : Term 2 1 2 = Tapp FZ (Var (FS FZ))
          edge : Term 2 1 1 = Tapp FZ (Var FZ)
          left : Term 2 1 1 = Tvar FZ
          right : Term 2 1 1 = Tvar (FS FZ) in
      accepted (checkSquare 12 ctx body left right edge edge) &&
      rejected (checkSquare 12 ctx body edge right left edge) &&
      rejected (checkSquare 12 ctx body left edge edge right))
  , ("square does not assume excluded middle",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          i : ScopedInterval 2 = Var FZ
          body : Term 2 1 2 = Tapp FZ (Meet i (Reverse i))
          zero : Term 2 1 1 = Tvar FZ in
      rejected (checkSquare 16 ctx body zero zero zero zero))
  , ("restricted telescope follows open endpoint chains",
      let ctx : Telescope 2 2 = Extend (Extend Empty (Tvar FZ) (Tvar (FS FZ)))
                                         (Tapp FZ Zero) (Tapp FZ One)
          face : Restriction 1 = Under (SEndpoint FZ False) in
      accepted (convertRestricted 12 face ctx (Tapp FZ (Var FZ)) (Tvar FZ)) &&
      rejected (convertRestricted 12 face ctx (Tapp FZ (Var FZ)) (Tvar (FS FZ))) &&
      exhausted (convertRestricted 11 face ctx (Tapp FZ (Var FZ)) (Tvar FZ)))
  , ("restricted telescope meet square, disjunction and empty faces",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          square : Term 2 1 2 = Tapp FZ (Meet (Var FZ) (Var (FS FZ)))
          zero : Restriction 2 = Under (SDisjunction (SEndpoint FZ False) (SEndpoint (FS FZ) False))
          one : Restriction 2 = Under (SConjunction (SEndpoint FZ True) (SEndpoint (FS FZ) True))
          empty : Restriction 2 = Under SBottom in
      accepted (convertRestricted 12 zero ctx square (Tvar FZ)) &&
      accepted (convertRestricted 12 one ctx square (Tvar (FS FZ))) &&
      accepted (convertRestricted 12 one ctx (Tapp FZ (Var FZ)) (Tapp FZ (Var (FS FZ)))) &&
      accepted (convertRestricted 12 empty ctx (Tvar FZ) (Tvar (FS FZ))) &&
      rejected (convertRestricted 12 one ctx square (Tvar FZ)))
  , ("restricted telescope respects non-Boolean dimensions and identities",
      let ctx : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar (FS FZ))
          same : Telescope 2 1 = Extend Empty (Tvar FZ) (Tvar FZ)
          ends : Restriction 1 = Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))
          i : ScopedInterval 1 = Var FZ in
      accepted (convertRestricted 12 ends same (Tapp FZ i) (Tvar FZ)) &&
      rejected (convertRestricted 12 ends ctx (Tapp FZ i) (Tvar FZ)) &&
      rejected (convertRestricted 12 unrestricted ctx (Tapp FZ (Meet i (Reverse i))) (Tvar FZ)) &&
      rejected (convertRestricted 12 unrestricted same (Tapp FZ i) (Tvar FZ)) &&
      accepted (convertRestricted 12 (Under (SEndpoint FZ False)) ctx
                (Tapp FZ i) (Tapp FZ Zero)))
  , ("restricted telescope does not equate distinct path names",
      let ctx : Telescope 1 2 = Extend (Extend Empty (Tvar FZ) (Tvar FZ)) (Tvar FZ) (Tvar FZ) in
      rejected (convertRestricted {n = 1} 12 unrestricted ctx (Tapp FZ (Var FZ)) (Tapp (FS FZ) (Var FZ))))
  , ("dependent telescope reduces open endpoints and checks boundaries",
      let ctx : Telescope 2 2 = Extend (Extend Empty (Tvar FZ) (Tvar (FS FZ)))
                                         (Tapp FZ Zero) (Tapp FZ One)
          body : Term 2 2 1 = Tapp FZ (Var FZ) in
      accepted (Telescope.convert {n = 1} 12 ctx (Tapp FZ Zero) (Tvar FZ)) &&
      accepted (Telescope.convert {n = 1} 12 ctx (Tapp FZ One) (Tvar (FS FZ))) &&
      accepted (checkBoundary 12 ctx body (Tvar FZ) (Tvar (FS FZ))) &&
      rejected (checkBoundary 12 ctx body (Tvar (FS FZ)) (Tvar (FS FZ))) &&
      rejected (Telescope.convert {n = 1} 12 ctx (Tapp FZ (Var FZ)) (Tapp (FS FZ) (Var FZ))) &&
      exhausted (Telescope.convert {n = 1} 2 ctx (Tvar FZ) (Tvar FZ)) &&
      accepted (Telescope.convert {n = 1} 12 ctx (mapDims (\_ => Zero) body) (Tvar FZ)))
  , ("finite context mappings preserve endpoints, identities and composition",
      let identity : ContextMapping 2 2 2 2 = MapContext [FZ, FS FZ] [FZ, FS FZ]
          swapPaths : ContextMapping 2 2 2 2 = MapContext [FZ, FS FZ] [FS FZ, FZ]
          collapse : ContextMapping 2 2 1 1 = MapContext [FZ, FZ] [FZ, FZ]
          collapsed : PathContext 1 1 = [PathBetween FZ FZ]
          reversed : PathContext 2 2 = [PathBetween (FS FZ) FZ, PathBetween (FS FZ) FZ]
          swapVars : ContextMapping 2 2 2 2 = MapContext [FS FZ, FZ] [FZ, FS FZ]
          body : ContextTerm 2 2 1 = ApplyPath FZ (Var FZ) in
      accepted (checkContextMapping 4 paths paths identity) &&
      exhausted (checkContextMapping 3 paths paths identity) &&
      rejected (checkContextMapping 4 paths paths swapVars) &&
      accepted (checkContextMapping 4 paths reversed swapVars) &&
      accepted (checkContextMapping 4 paths collapsed collapse) &&
      sameContextTerm (mapContextTerm identity body) body &&
      sameContextTerm (mapContextTerm swapPaths (mapContextTerm swapPaths body))
                      (mapContextTerm identity body) &&
      not (sameContextTerm (mapContextTerm swapPaths body) body) &&
      case checkBoundAbstraction 12 paths body FZ (FS FZ) of
        Left _ => False
        Right checked =>
          case (mapBoundContext 12 paths swapPaths checked,
                mapBoundContext 12 reversed swapVars checked,
                mapBoundContext 12 collapsed collapse checked) of
            (Right first, Right _, Right _) =>
              case (mapBoundContext 12 paths swapVars checked,
                    mapBoundContext 0 paths identity checked) of
                (Left Rejected, Left Exhausted) =>
                  case (mapBoundContext 12 paths swapPaths first,
                        mapBoundContext 12 paths identity checked) of
                    (Right _, Right _) => True
                    _ => False
                _ => False
            _ => False),
    ("bound context dimension substitution composition and exhaustion",
      let body : ContextTerm 2 2 2 = ApplyPath FZ (Meet (Var FZ) (Join (Var (FS FZ)) One)) in
      case checkBoundAbstraction 12 paths body FZ (FS FZ) of
        Left _ => False
        Right checked =>
          case (substituteBoundDimensions {d=1} 12 (\_ => Reverse (Var FZ)) checked,
                substituteBoundDimensions {d=1} 0 (\_ => Var FZ) checked,
                substituteBoundDimensions {d=1} 12 (\_ => reversals 11 (Var FZ)) checked) of
            (Right first, Left Exhausted, Left Exhausted) =>
              case (substituteBoundDimensions {d=1} 12 (\_ => Reverse (Var FZ)) first,
                    substituteBoundDimensions {d=1} 12 (\_ => Reverse (Reverse (Var FZ))) checked) of
                (Right _, Right _) =>
                  let rev : Fin 1 -> ScopedInterval 1 = \_ => Reverse (Var FZ) in
                  let twice = mapContextDimensions (liftContextDimensions rev)
                                (mapContextDimensions (liftContextDimensions rev) body)
                      direct = mapContextDimensions
                                 (liftContextDimensions (\i => substituteScoped rev (rev i))) body in
                  sameContextTerm twice direct &&
                  case (twice, direct) of
                    (ApplyPath FZ (Meet (Var FZ) (Join (Reverse (Reverse (Var (FS FZ)))) One)),
                     ApplyPath FZ (Meet (Var FZ) (Join (Reverse (Reverse (Var (FS FZ)))) One))) => True
                    _ => False
                _ => False
            _ => False)
  , ("finite substitution preflight counts duplicated output and unused environment",
      let env : Vect 1 (ScopedInterval 1) = [Reverse (Var FZ)]
          body : ContextTerm 2 2 2 = ApplyPath FZ (Meet (Var (FS FZ)) (Var (FS FZ)))
          unused : ContextTerm 2 2 2 = Variable FZ in
      not (boundedSubstitutionPreflight 8 env body) &&
      boundedSubstitutionPreflight 9 env body &&
      not (boundedSubstitutionPreflight 20 (the (Vect 1 (ScopedInterval 1)) [reversals 100 (Var FZ)]) unused) &&
      not (boundedSubstitutionPreflight {d=12} 100 [Zero] unused) &&
      not (boundedSubstitutionPreflight {m=13, k=0, n=0, d=0} 100 [] (Variable FZ)))
  , ("finite preflight exact environment and term accounting",
      let env : Vect 1 (ScopedInterval 0) = [Zero]
          body : ContextTerm 2 2 2 = Variable FZ in
      not (boundedSubstitutionPreflight 2 env body) &&
      boundedSubstitutionPreflight 3 env body)
  , ("finite preflight hard cap matches checker body admission",
      let body : ContextTerm 2 2 2 = ApplyPath FZ (Var (FS FZ))
          ten : Vect 1 (ScopedInterval 0) = [reversals 8 Zero]
          eleven : Vect 1 (ScopedInterval 0) = [reversals 9 Zero] in
      boundedSubstitutionPreflight 1000 ten body &&
      not (boundedSubstitutionPreflight 1000 eleven body) &&
      accepted (checkContextAbstraction {n=0} 1000
        (the (PathContext 1 1) [PathBetween FZ FZ])
        (ApplyPath FZ (reversals 8 Zero)) FZ FZ) &&
      exhausted (checkContextAbstraction {n=0} 1000
        (the (PathContext 1 1) [PathBetween FZ FZ])
        (ApplyPath FZ (reversals 9 Zero)) FZ FZ))
  , ("finite checked substitution enforces output cap with ample budget",
      let body : ContextTerm 2 2 2 = ApplyPath FZ (Join (Var FZ) (Meet (Var (FS FZ)) Zero))
          env : Vect 1 (ScopedInterval 0) = [reversals 8 Zero] in
      case checkBoundAbstraction 1000 paths body FZ (FS FZ) of
        Left _ => False
        Right checked => case substituteBoundDimensionsFinite 1000 env checked of
          Left Exhausted => True
          _ => False)
  , ("finite checked substitution preserves binder and reports exhaustion",
      let body : ContextTerm 2 2 2 = ApplyPath FZ (Meet (Var FZ) (Join (Var (FS FZ)) One))
          env : Vect 1 (ScopedInterval 1) = [Reverse (Var FZ)] in
      case checkBoundAbstraction 12 paths body FZ (FS FZ) of
        Left _ => False
        Right checked =>
          case (substituteBoundDimensionsFinite 12 env checked,
                substituteBoundDimensionsFinite 12 (the (Vect 1 (ScopedInterval 1)) [reversals 100 (Var FZ)]) checked) of
            (Right _, Left Exhausted) =>
              case mapContextDimensions (liftContextDimensions (\i => index i env)) body of
                ApplyPath FZ (Meet (Var FZ) (Join (Reverse (Var (FS FZ))) One)) => True
                _ => False
            _ => False)
  , ("finite preflight agrees with small exhaustive reference",
      let atoms : List (ScopedInterval 2) = [Zero, One, Var FZ, Var (FS FZ)]
          inputs = atoms ++ map Reverse atoms ++
                   concatMap (\x => map (Meet x) atoms ++ map (Join x) atoms) atoms
          replacements : List (ScopedInterval 1) = [Zero, One, Var FZ, Reverse (Var FZ)] in
      all (\r => all (\x => all (\fuel => preflightReference fuel r x) [0..20]) inputs) replacements)
  , ("finite preflight rejects exponential output growth",
      let env : Vect 1 (ScopedInterval 1) = [branching 8 (Var FZ)]
          body : ContextTerm 2 2 2 = ApplyPath FZ (Meet (Var (FS FZ)) (Var (FS FZ))) in
      not (boundedSubstitutionPreflight 100 env body) &&
      not (boundedSubstitutionPreflight 1200 env body) &&
      not (boundedSubstitutionPreflight 2000 env body))
  , ("mixed substitution commutes on a nonempty restricted face",
      let face : ScopedFace 1 = SEndpoint FZ False
          env : Fin 1 -> ScopedInterval 1 = \_ => Reverse (Var FZ)
          term : ContextTerm 2 2 1 = ApplyPath FZ (Var FZ)
          dimThenTerm = renameContextTerms FS (mapContextDimensions env term)
          termThenDim = mapContextDimensions env (renameContextTerms FS term)
          variable : ContextTerm 2 2 1 = Variable FZ
          renamedVariable = renameContextTerms FS (mapContextDimensions env variable)
          transformedFace = substituteScopedFace env face
          renamed = renameContext FS paths in
      sameContextTerm dimThenTerm termThenDim &&
      sameContextTerm renamedVariable (mapContextDimensions env (renameContextTerms FS variable)) &&
      sameContextTerm renamedVariable (Variable (FS FZ)) &&
      not (isEmptyRestriction (Under transformedFace)) &&
      accepted (convert 12 (Under face) paths term (Variable FZ)) &&
      accepted (convert 12 (Under transformedFace) renamed dimThenTerm (Variable (FS FZ))) &&
      accepted (convert 12 (Under transformedFace) renamed termThenDim (Variable (FS FZ))) &&
      rejected (convert 12 (Under face) renamed dimThenTerm (Variable (FS FZ))) &&
      rejected (convert 12 (Under transformedFace) renamed dimThenTerm (Variable (FS (FS FZ)))))
  , ("mixed dimension and variable substitution respects contradictory face",
      let face : ScopedFace 1 = SConjunction (SEndpoint FZ False) (SEndpoint FZ True)
          env : Fin 1 -> ScopedInterval 1 = \_ => Reverse (Var FZ)
          term : ContextTerm 2 2 1 = ApplyPath FZ (Var FZ) in
      accepted (convert 12 (Under (substituteScopedFace env face)) (renameContext FS paths)
        (renameContextTerms FS (mapContextDimensions env term)) (Variable FZ)))
  , ("context reversal and wrong boundary",
      accepted (checkContextAbstraction {n=0} 12 paths (ApplyPath (FS FZ) (Reverse (Var FZ))) (FS FZ) FZ) &&
      rejected (checkContextAbstraction {n=0} 12 paths (ApplyPath (FS FZ) (Reverse (Var FZ))) FZ (FS FZ)))
  , ("distinct paths and shared endpoints",
      rejected (convert {n=1} 12 unrestricted paths (ApplyPath FZ (Var FZ)) (ApplyPath (FS FZ) (Var FZ))) &&
      accepted (convert {n=1} 12 (Under (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))) paths (ApplyPath FZ (Var FZ)) (ApplyPath (FS FZ) (Var FZ))) &&
      accepted (convert {n=1} 12 (Under SBottom) paths (ApplyPath FZ Zero) (ApplyPath (FS FZ) One)))
  , ("opposite declarations meet at crossed endpoints only",
      let opposite : PathContext 3 2 = [PathBetween FZ (FS FZ), PathBetween (FS FZ) (FS (FS FZ))] in
      accepted (convert {n=0} 12 unrestricted opposite (ApplyPath FZ One) (ApplyPath (FS FZ) Zero)) &&
      rejected (convert {n=0} 12 unrestricted opposite (ApplyPath FZ Zero) (ApplyPath (FS FZ) One)))
  , ("context square faces",
      accepted (convert {n=2} 12 (Under (SEndpoint FZ False)) paths (ApplyPath FZ (Meet (Var FZ) (Var (FS FZ)))) (ApplyPath (FS FZ) Zero)) &&
      accepted (convert {n=2} 12 (Under (SEndpoint FZ True)) paths (ApplyPath (FS FZ) (Meet (Var FZ) (Var (FS FZ)))) (ApplyPath (FS FZ) (Var (FS FZ)))) &&
      rejected (convert {n=2} 12 (Under (SEndpoint FZ True)) paths (ApplyPath FZ (Meet (Var FZ) (Var (FS FZ)))) (ApplyPath (FS FZ) (Var (FS FZ)))))
  , ("context renaming and bounds",
      accepted (convert {n=1} 12 (Under (SEndpoint FZ False)) (renameContext FS paths) (renameContextTerms FS (ApplyPath FZ (Var FZ))) (Variable (FS FZ))) &&
      exhausted (convert {n=1} 2 unrestricted paths (ApplyPath FZ (Var FZ)) (ApplyPath FZ (Var FZ))) &&
      exhausted (convert {m=13, k=0, n=0} 100 unrestricted [] (Variable FZ) (Variable FZ)))
  , ("context twelve-node admission boundary",
      -- STop + ApplyPath + nine interval nodes + Variable = 12.
      let nine : ScopedInterval 0 = reversals 8 Zero
          ten : ScopedInterval 0 = reversals 9 Zero in
      accepted (convert {n=0} 100 unrestricted paths (ApplyPath FZ nine) (Variable FZ)) &&
      exhausted (convert {n=0} 100 unrestricted paths (ApplyPath FZ ten) (Variable (FS FZ))))
  , ("context index and dimension caps at twelve",
      accepted (convert {m=12, k=0, n=0} 100 unrestricted [] (Variable FZ) (Variable FZ)) &&
      exhausted (convert {m=13, k=0, n=0} 100 unrestricted [] (Variable FZ) (Variable FZ)) &&
      accepted (convert {m=2, k=12, n=0} 100 unrestricted (replicate 12 p) (ApplyPath FZ Zero) (Variable FZ)) &&
      exhausted (convert {m=2, k=13, n=0} 100 unrestricted (replicate 13 p) (ApplyPath FZ Zero) (Variable FZ)) &&
      accepted (convert {m=2, k=2, n=12} 100 unrestricted paths (Variable FZ) (Variable FZ)) &&
      exhausted (convert {m=2, k=2, n=13} 100 unrestricted paths (Variable FZ) (Variable FZ)))
  , ("oversized abstraction admitted before endpoint substitution",
      -- Ten reversals cancel semantically, including after substituting either endpoint.
      let large : ScopedInterval 1 = reversals 10 (Var FZ) in
      exhausted (checkContextAbstraction {n=0} 100 paths (ApplyPath FZ large) FZ (FS FZ)))
  , ("abstraction checks original dimension bound before substitution",
      let body : ContextTerm 2 2 13 = ApplyPath FZ (Var FZ)
          zero : ContextTerm 2 2 12 = mapContextDimensions (\i => case i of { FZ => Zero; FS j => Var j }) body in
      accepted (convert {n=12} 100 unrestricted paths zero (Variable FZ)) &&
      exhausted (checkContextAbstraction {n=12} 100 paths body FZ (FS FZ)))
  , ("abstraction retains older dimension when substituting newest",
      let body : ContextTerm 2 2 2 = ApplyPath FZ (Meet (Var FZ) (Join (Var (FS FZ)) One))
          end : ContextTerm 2 2 1 = mapContextDimensions (\i => case i of { FZ => One; FS j => Var j }) body in
      accepted (checkContextAbstraction {n=1} 12 paths body FZ (FS FZ)) &&
      case end of
        ApplyPath _ (Meet One (Join (Var FZ) One)) => True
        _ => False)
  , ("abstraction rejects older-dimension-dependent right endpoint",
      rejected (checkContextAbstraction {n=1} 12 paths
        (ApplyPath FZ (Meet (Var FZ) (Var (FS FZ)))) FZ (FS FZ)))
  , ("open neutral path abstraction", accepted (checkAbstraction {n=0} 12 p (At (Var FZ)) FZ (FS FZ)))
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
