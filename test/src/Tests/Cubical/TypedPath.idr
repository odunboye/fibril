module Tests.Cubical.TypedPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.FaceSoundness
import Fibril.Cubical.Logical.TypedPathChecker

import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope


%default total

-- All derivations are checked by Idris; neither endpoints nor the path type
-- are trusted annotations. The context is one variable of A.
constant : HasType {m = 1} {n = 0} (Abstract (Variable FZ))
  (Path Universe (Variable FZ) (Variable FZ))
constant = PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl

application : HasType {m = 1} {n = 0} (Apply (Abstract (Variable FZ)) Zero) Universe
application = PathElim constant Zero

nested : HasType {m = 1} {n = 0} (Abstract (Abstract (Variable FZ)))
  (Path (Path Universe (Variable FZ) (Variable FZ))
    (Abstract (Variable FZ)) (Abstract (Variable FZ)))
nested = PathIntro (PathForm Base (BaseVar FZ) (BaseVar FZ)) constant constant
  (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) Refl Refl

-- The body really depends on the bound dimension. This judgment does not
-- identify the two applications by beta conversion.
varying : HasType {m = 1} {n = 0}
  (Abstract (Apply (Abstract (Variable FZ)) (Var FZ)))
  (Path Universe (Apply (Abstract (Variable FZ)) Zero)
                 (Apply (Abstract (Variable FZ)) One))
varying = PathIntro Base (PathElim constant Zero) (PathElim constant One)
  (PathElim (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) (Var FZ)) Refl Refl

-- A neutral path declaration refers only to base variables.
neutralContext : PathContext 2 1
neutralContext = [PathBetween FZ (FS FZ)]

coincidentContext : PathContext 2 1
coincidentContext = [PathBetween FZ FZ]

neutralApplication : NeutralHasType Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NPath FZ) (Var FZ)) NType
neutralApplication = NElim (NPathVar FZ) (Var FZ)

neutralLeftRestricted : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
neutralLeftRestricted = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl

neutralMeetLeft : NeutralEqual {n = 2} Tests.Cubical.TypedPath.neutralContext (SEndpoint (FS FZ) False)
  (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))) (NBase FZ) NType
neutralMeetLeft = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl

nonBooleanFace : boundedFaceEntails {n = 1} STop
  (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)) = False
nonBooleanFace = Refl

-- Check each endpoint observation against both endpoint faces.
fourZeroAtZero : evalFace (fourValuation (const DZero)) (SEndpoint FZ False) = True
fourZeroAtZero = Refl

fourZeroAtOne : evalFace (fourValuation (const DZero)) (SEndpoint FZ True) = False
fourZeroAtOne = Refl

fourOneAtZero : evalFace (fourValuation (const DOne)) (SEndpoint FZ False) = False
fourOneAtZero = Refl

fourOneAtOne : evalFace (fourValuation (const DOne)) (SEndpoint FZ True) = True
fourOneAtOne = Refl

-- Neither non-endpoint observation satisfies the endpoint disjunction.
fourNonBooleanPositive : evalFace (fourValuation (const DPositive))
  (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)) = False
fourNonBooleanPositive = Refl

fourNonBooleanNegative : evalFace (fourValuation (const DNegative))
  (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)) = False
fourNonBooleanNegative = Refl

contradictoryEndpointAssumption : (v : Four) ->
  evalFace (fourValuation (const v))
    (SConjunction (SEndpoint FZ False) (SEndpoint FZ True)) = False
contradictoryEndpointAssumption DZero = Refl
contradictoryEndpointAssumption DOne = Refl
contradictoryEndpointAssumption DPositive = Refl
contradictoryEndpointAssumption DNegative = Refl

contradictionNotDetected : boundedFaceEntails {n = 1}
  (SConjunction (SEndpoint FZ False) (SEndpoint FZ True)) SBottom = False
contradictionNotDetected = Refl

soundnessExample : (env : Fin 1 -> Bool -> Bool) ->
  evalFace env (SConjunction (SEndpoint FZ False) (SEndpoint FZ True)) = True ->
  evalFace env (SEndpoint FZ False) = True
soundnessExample env = boundedFaceEntailsSound env
  (SConjunction (SEndpoint FZ False) (SEndpoint FZ True)) (SEndpoint FZ False) Refl

-- Both endpoints vary with the bound dimension.
varyingFamily : NeutralTypeFormed {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
varyingFamily = NPathForm NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))

pathPForm : NeutralTypeFormed {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
    (NAbstract (NApply (NPath FZ) Zero))
    (NAbstract (NApply (NPath FZ) One)))
pathPForm = NPathPForm varyingFamily
  (NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
    (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero)) (NRefl (NElim (NPathVar FZ) Zero)))
  (NIntro NBaseForm (NElim (NPathVar FZ) One) (NElim (NPathVar FZ) One)
    (NElim (NPathVar FZ) One) (NRefl (NElim (NPathVar FZ) One)) (NRefl (NElim (NPathVar FZ) One)))

pathPConstant : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))
pathPConstant = NPathPIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ)
  (NBaseVar FZ) (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))

pathPApplication : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) Zero) NType
pathPApplication = NPathPElim pathPConstant Zero

pathPLeft : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) Zero) (NBase FZ) NType
pathPLeft = NPathPEndpointLeft pathPConstant (NBaseVar FZ) Refl

-- Elimination computes the family at the supplied interval, rather than
-- returning the uninstantiated family or a fixed carrier.
varyingElimination : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop p
  (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ))) l r) ->
  NeutralHasType Tests.Cubical.TypedPath.neutralContext STop (NApply p One)
    (NPathType NType (NApply (NPath FZ) One) (NApply (NPath FZ) One))
varyingElimination h = NPathPElim h One

pathPRight : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) One) (NBase FZ) NType
pathPRight = NPathPEndpointRight pathPConstant (NBaseVar FZ) Refl

-- Substitution reaches the outer dimension beneath the abstraction, without
-- capturing or replacing its freshly bound dimension.
pathPSubstitutionShadowing :
  mapNeutralDimensions (instantiateDimension Zero)
    (NAbstract (NApply (NPath {m = 2} {k = 1} FZ)
      (Meet (Var FZ) (Var (FS FZ))))) =
  NAbstract (NApply (NPath FZ) (Meet (Var FZ) Zero))
pathPSubstitutionShadowing = Refl

-- Conditional on a path-over of the varying family: the endpoint is actually
-- derived at the family instantiated at Zero, rather than assumed at a carrier.
varyingEndpointAtZero :
  NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop p
    (NPathType
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NAbstract (NApply (NPath FZ) Zero))
      (NAbstract (NApply (NPath FZ) One))) ->
  NeutralEqual Tests.Cubical.TypedPath.neutralContext STop
    (NApply p Zero) (NAbstract (NApply (NPath FZ) Zero))
    (NPathType NType (NApply (NPath FZ) Zero) (NApply (NPath FZ) Zero))
varyingEndpointAtZero h = NPathPEndpointLeft h
  (NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
    (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero))
    (NRefl (NElim (NPathVar FZ) Zero))) Refl

-- The endpoint derivation itself is concrete at the open instantiated carrier.
-- This particular path-over remains a hypothetical judgment; the separate
-- square derivation below constructs a different varying family.
varyingEndpointAtOpenZero :
  NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False) p
    (NPathType
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
      (NAbstract (NApply (NPath FZ) One))) ->
  NeutralEqual Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NApply p (Var FZ)) (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
    (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
varyingEndpointAtOpenZero h = NPathPEndpointLeft h
  (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))) Refl

-- Congruence is restricted to the very face on which the endpoint equality
-- was established; both source and target path types are formed there.
restrictedPathTypeCongruence :
  NeutralTypeEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
    (NPathType NType (NBase FZ) (NBase FZ))
restrictedPathTypeCongruence = NPathTypeCong NBaseForm
  (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
  (NBaseVar FZ) (NBaseVar FZ) neutralLeftRestricted neutralLeftRestricted

restrictedConvertedPath :
  NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
    (NPathType NType (NBase FZ) (NBase FZ))
restrictedConvertedPath = NConvert
  (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ)))))
  restrictedPathTypeCongruence

-- The inner edge of the square, with the outer dimension still free.
squareInner : NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
  (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))
squareInner = NIntro NBaseForm (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
  (NElim (NPathVar FZ) (Meet (Var (FS FZ)) (Var FZ)))
  (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
  (NIntervalApplyCong (NPathVar FZ) (IMeetRightOne Refl))

squareRightCong : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ)) NType
squareRightCong = NIntervalApplyCong (NPathVar FZ) (IMeetRightOne Refl)

dependentAbstractRefl : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NAbstract (NBase FZ))
  (NPathType NType (NBase FZ) (NBase FZ))
dependentAbstractRefl = NPathPAbstractCong pathPConstant pathPConstant (NRefl (NBaseVar FZ))

-- The actual square: the outer PathP family has right endpoint p i.
leftEdge : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))
leftEdge = NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ)
  (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))

rightEdge : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NApply (NPath FZ) (Var FZ)))
  (NPathType NType (NBase FZ) (NBase (FS FZ)))
rightEdge = NIntro NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
  (NElim (NPathVar FZ) (Var FZ))
  (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
  (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl)

square : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ)))))
  (NPathType (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))
    (NAbstract (NBase FZ)) (NAbstract (NApply (NPath FZ) (Var FZ))))
square = NPathPIntro
  (NPathForm NBaseForm (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ)))
  (NConvert leftEdge (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar FZ)
    (NBaseVar FZ) (NElim (NPathVar FZ) Zero) (NRefl (NBaseVar FZ))
    (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))))
  (NConvert rightEdge (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
    (NBaseVar FZ) (NElim (NPathVar FZ) One) (NRefl (NBaseVar FZ))
    (NSym (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))))
  squareInner
  (NAbstractCong {a = NType}
    (NFaceRestrict squareInner Refl)
    (NConvert
      (NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ)
        (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ)))
      (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar FZ)
        (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
        (NRefl (NBaseVar FZ))
        (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))))
    (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))
  (NAbstractCong {a = NType}
    (NFaceRestrict squareInner Refl)
    (NConvert
      (NIntro NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
        (NElim (NPathVar FZ) (Var FZ))
        (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
        (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))
      (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
        (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
        (NRefl (NBaseVar FZ)) (NSym (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))))
    (NIntervalApplyCong (NPathVar FZ) (IMeetLeftOne Refl)))

convertedEquality : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
  (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
  (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
  (NPathType NType (NBase FZ) (NBase FZ))
convertedEquality = NEqualConvert
  (NRefl (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))))
  restrictedPathTypeCongruence restrictedConvertedPath restrictedConvertedPath

checkerSuccess : Either CheckError a -> Bool
checkerSuccess (Right _) = True
checkerSuccess _ = False

checkerRejected : Either CheckError a -> Bool
checkerRejected (Left _) = True
checkerRejected (Right _) = False

checkerSemanticRejected : Either CheckError a -> Bool
checkerSemanticRejected (Left Mismatch) = True
checkerSemanticRejected (Left Unsupported) = True
checkerSemanticRejected _ = False

checkerMismatch : Either CheckError a -> Bool
checkerMismatch (Left Mismatch) = True
checkerMismatch _ = False

checkerExhausted : Either CheckError a -> Bool
checkerExhausted (Left Exhausted) = True
checkerExhausted _ = False

checkerUnsupported : Either CheckError a -> Bool
checkerUnsupported (Left Unsupported) = True
checkerUnsupported _ = False

escapeOriginal : NeutralExpr 2 1 0
escapeOriginal = NPathType NType (NBase FZ) (NBase (FS FZ))
escapeSource : NeutralExpr 2 1 0
escapeSource = NPathType NType (NBase FZ) (NApply (NPath FZ) One)
escapeMiddle : NeutralExpr 2 1 0
escapeMiddle = NPathType NType (NBase FZ) (NApply (NPath FZ) (Meet One One))
escapeTarget : NeutralExpr 2 1 0
escapeTarget = NPathType NType (NBase FZ) (NApply (NPath FZ) (Meet (Meet One One) One))

-- Both types have globally valid typings, obtained by two separate meet-one
-- conversions; the checker cannot combine those steps on STop.
equalityConversionFaceEscape : Bool
equalityConversionFaceEscape =
  case (checkNeutralTypeEqual {n = 0} 96 neutralContext STop escapeOriginal escapeSource,
        checkNeutralTypeEqual {n = 0} 96 neutralContext STop escapeSource escapeMiddle,
        checkNeutralTypeEqual {n = 0} 96 neutralContext STop escapeMiddle escapeTarget) of
    (Right first, Right second, Right third) =>
      let basePath : NeutralHasType Tests.Cubical.TypedPath.neutralContext STop (NPath FZ) escapeOriginal = NPathVar FZ
          src = NConvert basePath first
          dst = NConvert (NConvert src second) third
          restrictedSrc = NFaceRestrict src Refl
          restrictedDst = NFaceRestrict dst Refl in
      checkerUnsupported (convertNeutralEquality 96 neutralContext STop
        (NPath FZ) (NPath FZ) escapeSource escapeTarget (NRefl src) dst dst) &&
      checkerSuccess (convertNeutralEquality 96 neutralContext SBottom
        (NPath FZ) (NPath FZ) escapeSource escapeTarget (NRefl restrictedSrc) restrictedDst restrictedDst)
    _ => False

-- Independent one-variable reference for every interval of depth at most one.
referenceInterval : ScopedInterval 0 -> ScopedInterval 1 -> ScopedInterval 0
referenceInterval replacement Zero = Zero
referenceInterval replacement One = One
referenceInterval replacement (Var FZ) = replacement
referenceInterval replacement (Reverse x) = Reverse (referenceInterval replacement x)
referenceInterval replacement (Meet x y) = Meet (referenceInterval replacement x) (referenceInterval replacement y)
referenceInterval replacement (Join x y) = Join (referenceInterval replacement x) (referenceInterval replacement y)

sameInterval : ScopedInterval 0 -> ScopedInterval 0 -> Bool
sameInterval Zero Zero = True
sameInterval One One = True
sameInterval (Reverse x) (Reverse y) = sameInterval x y
sameInterval (Meet x y) (Meet a b) = sameInterval x a && sameInterval y b
sameInterval (Join x y) (Join a b) = sameInterval x a && sameInterval y b
sameInterval _ _ = False

smallIntervals : List (ScopedInterval 1)
smallIntervals = let atoms = [Zero, One, Var FZ] in
  atoms ++ map Reverse atoms ++ concatMap (\x => map (Meet x) atoms) atoms ++
  concatMap (\x => map (Join x) atoms) atoms

substitutionReference : Bool
substitutionReference = all (\replacement => all (\i =>
  case boundedInstantiate {m = 2} {k = 1} 128 replacement (NApply (NPath FZ) i) of
    Right (NApply (NPath FZ) actual) => sameInterval actual (referenceInterval replacement i)
    _ => False) smallIntervals) (the (List (ScopedInterval 0)) [Zero, One])

squareFamily : NeutralExpr 2 1 1
squareFamily = NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ))

squareTerm : NeutralExpr 2 1 0
squareTerm = NAbstract (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))

squareLeft : NeutralExpr 2 1 0
squareLeft = NAbstract (NBase FZ)

squareRight : NeutralExpr 2 1 0
squareRight = NAbstract (NApply (NPath FZ) (Var FZ))

-- A genuinely varying family that duplicates its parameter in both endpoints.
duplicatingFamily : NeutralExpr 2 1 2
duplicatingFamily = NPathType NType
  (NApply (NPath FZ) (Meet (Var FZ) (Var FZ)))
  (NApply (NPath FZ) (Meet (Var FZ) (Var FZ)))

constantEdgeAt : (face : ScopedFace n) -> (i : ScopedInterval n) ->
  boundedFaceEntails face (scopedEndpoint i False) = True ->
  NeutralHasType Tests.Cubical.TypedPath.neutralContext face (NAbstract (NBase FZ))
    (NPathType NType (NApply (NPath FZ) i) (NApply (NPath FZ) i))
constantEdgeAt face i endpoint = NConvert
  (NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ)
    (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ)))
  (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar FZ)
    (NElim (NPathVar FZ) i) (NElim (NPathVar FZ) i)
    (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) endpoint))
    (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) endpoint)))

duplicatingPath : NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext SBottom
  (NAbstract (NAbstract (NBase FZ)))
  (NPathType Tests.Cubical.TypedPath.duplicatingFamily (NAbstract (NBase FZ)) (NAbstract (NBase FZ)))
duplicatingPath = NPathPIntro
  (NPathForm NBaseForm
    (NElim (NPathVar FZ) (Meet (Var FZ) (Var FZ)))
    (NElim (NPathVar FZ) (Meet (Var FZ) (Var FZ))))
  (constantEdgeAt SBottom (Meet Zero Zero) Refl)
  (constantEdgeAt SBottom (Meet One One) Refl)
  (constantEdgeAt SBottom (Meet (Var FZ) (Var FZ)) Refl)
  (NRefl (constantEdgeAt (SConjunction SBottom (SEndpoint FZ False))
    (Meet (Var FZ) (Var FZ)) Refl))
  (NRefl (constantEdgeAt (SConjunction SBottom (SEndpoint FZ True))
    (Meet (Var FZ) (Var FZ)) Refl))

nonBooleanArgument : ScopedInterval 1
nonBooleanArgument = Meet (Var FZ) (Reverse (Var FZ))

duplicatedInstance : NeutralExpr 2 1 1
duplicatedInstance = NPathType NType
  (NApply (NPath FZ) (Meet nonBooleanArgument nonBooleanArgument))
  (NApply (NPath FZ) (Meet nonBooleanArgument nonBooleanArgument))

-- Independent counters mirror the grammar, not the checker's private allowance.
testIntervalSize : ScopedInterval n -> Nat
testIntervalSize Zero = 1
testIntervalSize One = 1
testIntervalSize (Var _) = 1
testIntervalSize (Reverse x) = 1 + testIntervalSize x
testIntervalSize (Meet x y) = 1 + testIntervalSize x + testIntervalSize y
testIntervalSize (Join x y) = 1 + testIntervalSize x + testIntervalSize y

testExprSize : NeutralExpr m k n -> Nat
testExprSize (NBase _) = 1
testExprSize (NPath _) = 1
testExprSize NType = 1
testExprSize (NPathType a l r) = 1 + testExprSize a + testExprSize l + testExprSize r
testExprSize (NAbstract x) = 1 + testExprSize x
testExprSize (NApply p i) = 1 + testExprSize p + testIntervalSize i

duplicatePreflightTest : Bool
duplicatePreflightTest =
  let p : NeutralExpr 2 1 1 = NAbstract (NAbstract (NBase FZ))
      edge : NeutralExpr 2 1 1 = NAbstract (NBase FZ)
      -- SBottom counts one node. This independently establishes admission.
      admitted = 1 + testExprSize p + testIntervalSize nonBooleanArgument +
        testExprSize duplicatingFamily + testExprSize edge + testExprSize edge + testExprSize (the (NeutralExpr 2 1 1) NType)
      expansion = testIntervalSize nonBooleanArgument + testExprSize duplicatingFamily +
        testExprSize duplicatedInstance in
  admitted == 25 && expansion == 40 && admitted <= 39 &&
  checkerExhausted (boundedInstantiate 39 nonBooleanArgument duplicatingFamily) &&
  (case boundedInstantiate 40 nonBooleanArgument duplicatingFamily of
    Right (NPathType NType
      (NApply (NPath FZ) (Meet (Meet (Var FZ) (Reverse (Var FZ))) (Meet (Var FZ) (Reverse (Var FZ)))))
      (NApply (NPath FZ) (Meet (Meet (Var FZ) (Reverse (Var FZ))) (Meet (Var FZ) (Reverse (Var FZ)))))) => True
    _ => False) &&
  checkerExhausted (checkDependentApplication 39 neutralContext SBottom (NAbstract (NAbstract (NBase FZ))) nonBooleanArgument
    duplicatingFamily (NAbstract (NBase FZ)) (NAbstract (NBase FZ)) NType duplicatingPath)

autoFamily : NeutralExpr 2 1 1
autoFamily = NPathType NType (NApply (NPath FZ) (Var FZ))
  (NApply (NPath FZ) (Var FZ))

autoType : NeutralExpr 2 1 0
autoType = NPathType autoFamily (NPath FZ) (NPath FZ)

public export
checkerChecks : List (String, Bool)
checkerChecks =
  [ ("autonomous square exact shared work budget", checkerSuccess
      (checkDependentIntroduction {n = 0} 223 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous square one token short has no witness", checkerExhausted
      (checkDependentIntroduction {n = 0} 222 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous square branching budget exhausted", checkerExhausted
      (checkDependentIntroduction {n = 0} 128 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous exact exhaustion does not retry fallback", checkerExhausted
      (checkDependentIntroduction {n = 0} 3 neutralContext STop
        (NAbstract (NApply (NPath FZ) (Var FZ)))
        (NPathType NType (NBase (FS FZ)) (NBase (FS FZ)))))
  , ("autonomous failed fallback exact shared work budget", checkerUnsupported
      (checkDependentIntroduction {n = 0} 22 neutralContext STop
        (NAbstract (NApply (NPath FZ) (Var FZ)))
        (NPathType NType (NBase (FS FZ)) (NBase (FS FZ)))))
  , ("autonomous failed fallback one token short", checkerExhausted
      (checkDependentIntroduction {n = 0} 21 neutralContext STop
        (NAbstract (NApply (NPath FZ) (Var FZ)))
        (NPathType NType (NBase (FS FZ)) (NBase (FS FZ)))))
  , ("autonomous nested constant top", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop
        (NAbstract (NAbstract (NBase FZ)))
        (NPathType (NPathType NType (NBase FZ) (NBase FZ))
          (NAbstract (NBase FZ)) (NAbstract (NBase FZ)))))
  , ("autonomous nested wrong boundary rejected", checkerMismatch
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop
        (NAbstract (NAbstract (NBase FZ)))
        (NPathType (NPathType NType (NBase FZ) (NBase FZ))
          (NAbstract (NBase FZ)) (NAbstract (NBase (FS FZ))))))
  , ("autonomous connection square top", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous swapped connection square top", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop
        (NAbstract (NAbstract (NApply (NPath FZ) (Meet (Var FZ) (Var (FS FZ))))))
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous square nonzero path index", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048
        (the (PathContext 2 2) [PathBetween FZ (FS FZ), PathBetween (FS FZ) FZ]) STop
        (NAbstract (NAbstract (NApply (NPath (FS FZ)) (Meet (Var (FS FZ)) (Var FZ)))))
        (NPathType (NPathType NType (NBase (FS FZ)) (NApply (NPath (FS FZ)) (Var FZ)))
          (NAbstract (NBase (FS FZ))) (NAbstract (NApply (NPath (FS FZ)) (Var FZ))))))
  , ("autonomous square restricted endpoint does not escape", checkerSemanticRejected
      (checkDependentIntroduction {n = 1} 2048 neutralContext STop
        (NAbstract (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ)))))
        (NPathType (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))
          (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
          (NAbstract (NApply (NPath FZ) (Var FZ))))))
  , ("autonomous square bad left boundary rejected", checkerSemanticRejected
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop squareTerm
        (NPathType squareFamily (NAbstract (NBase (FS FZ))) squareRight)))
  , ("autonomous square bad right boundary rejected", checkerSemanticRejected
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft (NAbstract (NBase FZ)))))
  , ("autonomous square nonboolean boundary rejected", checkerSemanticRejected
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop squareTerm
        (NPathType squareFamily
          (NAbstract (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ))))) squareRight)))
  , ("autonomous square budget exhausted", checkerExhausted
      (checkDependentIntroduction {n = 0} 8 neutralContext STop squareTerm
        (NPathType squareFamily squareLeft squareRight)))
  , ("autonomous varying body top", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop
        (NAbstract (NApply (NPath FZ) (Var FZ)))
        (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("autonomous varying body wrong endpoint", checkerUnsupported
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop
        (NAbstract (NApply (NPath FZ) (Var FZ)))
        (NPathType NType (NBase (FS FZ)) (NBase (FS FZ)))))
  , ("autonomous varying family bottom", checkerSuccess
      (checkDependentIntroduction 2048 neutralContext SBottom (NAbstract (NPath FZ)) autoType))
  , ("autonomous varying family top rejected", checkerUnsupported
      (checkDependentIntroduction 2048 neutralContext STop (NAbstract (NPath FZ)) autoType))
  , ("autonomous wrong endpoint", checkerMismatch
      (checkDependentIntroduction 2048 neutralContext SBottom (NAbstract (NPath FZ))
        (NPathType autoFamily (NBase FZ) (NPath FZ))))
  , ("autonomous wrong body", checkerMismatch
      (checkDependentIntroduction 2048 neutralContext SBottom (NAbstract (NBase FZ)) autoType))
  , ("autonomous size exhausted", checkerExhausted
      (checkDependentIntroduction 3 neutralContext SBottom (NAbstract (NPath FZ)) autoType))
  , ("autonomous dimension exhausted", checkerExhausted
      (checkDependentIntroduction {n = 12} 2048 neutralContext SBottom
        (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))))
  , ("autonomous nonboolean family bottom", checkerSuccess
      (checkDependentIntroduction {n = 0} 2048 neutralContext SBottom (NAbstract (NPath FZ))
        (NPathType (NPathType NType
          (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ))))
          (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ))))) (NPath FZ) (NPath FZ))))
  , ("autonomous nonboolean family top rejected", checkerUnsupported
      (checkDependentIntroduction {n = 0} 2048 neutralContext STop (NAbstract (NPath FZ))
        (NPathType (NPathType NType
          (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ))))
          (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ))))) (NPath FZ) (NPath FZ))))
  , ("varying family application at i meet reverse i", checkerSuccess
      (checkDependentApplication 128 neutralContext SBottom
        (NAbstract (NAbstract (NBase FZ))) nonBooleanArgument duplicatingFamily
        (NAbstract (NBase FZ)) (NAbstract (NBase FZ)) duplicatedInstance duplicatingPath))
  , ("varying family nonboolean instance is not zero", checkerMismatch
      (checkDependentApplication 128 neutralContext SBottom
        (NAbstract (NAbstract (NBase FZ))) nonBooleanArgument duplicatingFamily
        (NAbstract (NBase FZ)) (NAbstract (NBase FZ))
        (NPathType NType (NApply (NPath FZ) (Meet Zero Zero))
          (NApply (NPath FZ) (Meet Zero Zero))) duplicatingPath))
  , ("dependent application expanded output preflight", duplicatePreflightTest)
  , ("dependent application of square at zero", checkerSuccess
      (checkDependentApplication 128 neutralContext STop squareTerm Zero squareFamily squareLeft squareRight
        (NPathType NType (NBase FZ) (NApply (NPath FZ) Zero)) square))
  , ("dependent application of square at one", checkerSuccess
      (checkDependentApplication 128 neutralContext STop squareTerm One squareFamily squareLeft squareRight
        (NPathType NType (NBase FZ) (NApply (NPath FZ) One)) square))
  , ("dependent application wrong family instance", checkerMismatch
      (checkDependentApplication 128 neutralContext STop squareTerm One squareFamily squareLeft squareRight
        (NPathType NType (NBase FZ) (NApply (NPath FZ) Zero)) square))
  , ("dependent application exhausted", checkerExhausted
      (checkDependentApplication 1 neutralContext STop squareTerm Zero squareFamily squareLeft squareRight
        (NPathType NType (NBase FZ) (NApply (NPath FZ) Zero)) square))
  , ("dependent application coincident endpoints", checkerSuccess
      (checkDependentApplication {n = 0} 64 coincidentContext STop (NPath FZ) One NType
        (NBase FZ) (NBase FZ) NType (NPathVar FZ)))
  , ("dependent application nonboolean interval", checkerSuccess
      (checkDependentApplication {n = 1} 64 neutralContext STop (NPath FZ)
        (Meet (Var FZ) (Reverse (Var FZ))) NType (NBase FZ) (NBase (FS FZ)) NType (NPathVar FZ)))
  , ("small exhaustive substitution reference", substitutionReference)
  , ("dependent formation", checkerSuccess (checkDependentFormation {n = 0} 128 neutralContext STop
      (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
        (NAbstract (NApply (NPath FZ) Zero)) (NAbstract (NApply (NPath FZ) One)))))
  , ("dependent wrong endpoint", checkerUnsupported (checkDependentFormation {n = 0} 128 neutralContext STop
      (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
        (NAbstract (NApply (NPath FZ) One)) (NAbstract (NApply (NPath FZ) One)))))
  , ("dependent wrong family", checkerUnsupported (checkDependentFormation {n = 0} 128 neutralContext STop
      (NPathType (NBase FZ) (NBase FZ) (NBase FZ))))
  , ("nested binder substitution", case boundedInstantiate {m = 2} {k = 1} {n = 0} 32 One
      (NAbstract (NApply (NPath FZ) (Meet (Var FZ) (Var (FS FZ))))) of
        Right (NAbstract (NApply (NPath FZ) (Meet (Var FZ) One))) => True
        _ => False)
  -- Input replacement: 3 nodes, source: 8 nodes, expanded output: 12 nodes.
  , ("open nested substitution exact budget", case boundedInstantiate {m = 2} {k = 1} {n = 1} 23
      (Meet (Var FZ) One)
      (NAbstract (NApply (NPath FZ) (Join (Var FZ) (Meet (Var (FS FZ)) (Var (FS FZ)))))) of
        Right (NAbstract (NApply (NPath FZ) (Join (Var FZ)
          (Meet (Meet (Var (FS FZ)) One) (Meet (Var (FS FZ)) One))))) => True
        _ => False)
  , ("open nested substitution one short", checkerExhausted (boundedInstantiate {m = 2} {k = 1} {n = 1} 22
      (Meet (Var FZ) One)
      (NAbstract (NApply (NPath FZ) (Join (Var FZ) (Meet (Var (FS FZ)) (Var (FS FZ))))))))
  , ("dependent dimension cap", checkerExhausted (checkDependentFormation {n = 12} 128 neutralContext STop
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("substitution expanded copies charged", checkerExhausted (boundedInstantiate {m = 2} {k = 1} {n = 0} 12
      (Meet Zero One) (NApply (NPath FZ) (Meet (Var FZ) (Var FZ)))))
  , ("typing conversion on endpoint face", checkerSuccess (convertNeutralTyping {n = 1} 64 neutralContext (SEndpoint FZ False)
      (NPath FZ) (NPathType NType (NBase FZ) (NBase (FS FZ)))
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ))) (NPathVar FZ)))
  , ("typing conversion cannot escape face", checkerUnsupported (convertNeutralTyping {n = 1} 64 neutralContext STop
      (NPath FZ) (NPathType NType (NBase FZ) (NBase (FS FZ)))
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ))) (NPathVar FZ)))
  , ("typing conversion exhaustion", checkerExhausted (convertNeutralTyping {n = 0} 1 neutralContext STop
      (NBase FZ) NType NType (NBaseVar FZ)))
  , ("typing restriction", checkerSuccess (restrictNeutralTyping {n = 1} 32 neutralContext STop (SEndpoint FZ False)
      (NBase FZ) NType (NBaseVar FZ)))
  , ("typing restriction rejects escape", checkerUnsupported (restrictNeutralTyping {n = 1} 32 neutralContext (SEndpoint FZ False) STop
      (NBase FZ) NType (NBaseVar FZ)))
  , ("typing restriction admission exhaustion", checkerExhausted (restrictNeutralTyping {n = 1} 1 neutralContext STop (SEndpoint FZ False)
      (NBase FZ) NType (NBaseVar FZ)))
  , ("square left endpoint type conversion", checkerSuccess (convertNeutralTyping {n = 0} 64 neutralContext STop
      (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))
      (NPathType NType (NBase FZ) (NApply (NPath FZ) Zero)) leftEdge))
  , ("face-sensitive equality conversion", checkerSuccess (convertNeutralEquality {n = 1} 96 neutralContext (SEndpoint FZ False)
      (NAbstract (NApply (NPath FZ) (Var (FS FZ)))) (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase FZ))
      (NRefl (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
        (NElim (NPathVar FZ) (Var (FS FZ)))
        (NRefl (NElim (NPathVar FZ) (Var (FS FZ)))) (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))))
      restrictedConvertedPath restrictedConvertedPath))
  , ("equality conversion", checkerSuccess (convertNeutralEquality {n = 0} 32 neutralContext STop
      (NBase FZ) (NBase FZ) NType NType (NRefl (NBaseVar FZ)) (NBaseVar FZ) (NBaseVar FZ)))
  , ("equality conversion admission exhaustion", checkerExhausted (convertNeutralEquality {n = 0} 1 neutralContext STop
      (NBase FZ) (NBase FZ) NType NType (NRefl (NBaseVar FZ)) (NBaseVar FZ) (NBaseVar FZ)))
  , ("equality conversion succeeds on bottom but direct global check is unsupported", equalityConversionFaceEscape)
  , ("checker path abstraction equality", checkerSuccess (checkNeutralPathEqual {n = 0} 64 coincidentContext SBottom
      (NAbstract (NApply (NPath FZ) (Var FZ))) (NAbstract (NBase FZ))
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker path abstraction face escape", checkerUnsupported (checkNeutralPathEqual {n = 0} 64 coincidentContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ))) (NAbstract (NBase FZ))
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker path abstraction wrong endpoint", checkerMismatch (checkNeutralPathEqual {n = 0} 64 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ))) (NAbstract (NBase FZ))
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker path abstraction exhaustion", checkerExhausted (checkNeutralPathEqual {n = 0} 1 neutralContext STop
      (NAbstract (NBase FZ)) (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker base reflexivity", checkerSuccess (checkNeutralEqual {n = 0} 32 neutralContext STop (NBase FZ) (NBase FZ)))
  , ("checker base mismatch", checkerMismatch (checkNeutralEqual {n = 0} 32 neutralContext STop (NBase FZ) (NBase (FS FZ))))
  , ("checker arbitrary interval reflexivity", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Reverse (Var FZ))) (NApply (NPath FZ) (Reverse (Var FZ)))))
  , ("checker left meet arbitrary factor", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Meet One (Reverse (Var FZ)))) (NApply (NPath FZ) (Reverse (Var FZ)))))
  , ("checker symmetric meet", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Reverse (Var FZ))) (NApply (NPath FZ) (Meet (Reverse (Var FZ)) One))))
  , ("checker symmetric endpoint", checkerSuccess (checkNeutralEqual {n = 0} 32 neutralContext STop
      (NBase (FS FZ)) (NApply (NPath FZ) One)))
  , ("checker unrelated paths", checkerMismatch (checkNeutralEqual {m = 2} {n = 0} 32
      [PathBetween FZ (FS FZ), PathBetween FZ (FS FZ)] STop
      (NApply (NPath FZ) Zero) (NApply (NPath (FS FZ)) Zero)))
  , ("checker path type face congruence", checkerSuccess (checkNeutralTypeEqual {n = 1} 64 neutralContext (SEndpoint FZ False)
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker path type face escape", checkerUnsupported (checkNeutralTypeEqual {n = 1} 64 neutralContext STop
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase FZ))))
  , ("checker path type exhaustion", checkerExhausted (checkNeutralTypeEqual {n = 0} 1 neutralContext STop NType NType))
  , ("checker connection inner edge", checkerSuccess (checkNeutral {n = 1} 64 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
      (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))))
  , ("checker connection wrong endpoint", checkerMismatch (checkNeutral {n = 1} 64 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
      (NPathType NType (NBase (FS FZ)) (NApply (NPath FZ) (Var FZ)))))
  , ("checker meet congruence", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ))))
  , ("checker face escape rejected", checkerUnsupported (checkNeutralEqual {n = 2} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) (Var (FS FZ)))) (NApply (NPath FZ) (Var FZ))))
  , ("checker non-boolean meet rejected", checkerUnsupported (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ)))) (NBase FZ)))
  , ("checker endpoint conversion", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext (SEndpoint FZ False)
      (NApply (NPath FZ) (Var FZ)) (NBase FZ)))
  , ("checker coincident endpoint zero", checkerSuccess (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) Zero) (NBase FZ)))
  , ("checker coincident endpoint one", checkerSuccess (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker coincident disjunctive right goal", checkerSuccess (checkNeutralEqual {n = 2} 64 coincidentContext (SEndpoint FZ True)
      (NApply (NPath FZ) (Join (Var FZ) (Var (FS FZ)))) (NBase FZ)))
  , ("checker disjunctive face not entailed", checkerUnsupported (checkNeutralEqual {n = 1} 64 coincidentContext
      (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))
      (NApply (NPath FZ) (Var FZ)) (NBase FZ)))
  , ("checker coincident endpoint wrong target", checkerMismatch (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) One) (NBase (FS FZ))))
  , ("checker matching left without entailment", checkerUnsupported (checkNeutralEqual {n = 0} 32 neutralContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker coincident endpoint exhausted", checkerExhausted (checkNeutralEqual {n = 0} 1 coincidentContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker equality exhausted", checkerExhausted (checkNeutralEqual {n = 1} 2 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ))))
  , ("checker open abstraction", checkerSuccess (checkNeutral {n = 0} 32 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker false face", checkerSuccess (checkNeutral {n = 1} 32 neutralContext SBottom
      (NApply (NPath FZ) (Var FZ)) NType))
  , ("checker annotation mismatch", checkerMismatch (checkNeutral {n = 0} 32 neutralContext STop
      (NPath FZ) (NPathType NType (NBase (FS FZ)) (NBase FZ))))
  , ("checker exhausted", checkerExhausted (checkNeutral {n = 1} 2 neutralContext STop
      (NApply (NPath FZ) (Var FZ)) NType))
  , ("checker unsupported", checkerUnsupported (checkNeutral {n = 0} 32 neutralContext STop
      (NAbstract (NAbstract (NBase FZ))) NType))
  , ("checker entailment limit fails closed", checkerUnsupported (checkNeutral {n = 12} 32 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker good annotation", checkerSuccess (checkNeutral {n = 0} 32 neutralContext STop
      (NPath FZ) (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker formation", checkerSuccess (checkNeutralFormation {n = 0} 32 neutralContext STop
      (NPathType NType (NApply (NPath FZ) Zero) (NBase FZ))))
  ]
