module Tests.Main

import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Usage
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Tests.Cubical.CommonEqualityAdmission
import Tests.Cubical.CommonAdmission
import Tests.Shadow
import Tests.Reduction
import Tests.Erased
import Tests.Pretty
import Tests.SourceText
import Tests.UTF8
import Tests.Lexer
import Tests.Frontend
import Tests.Compatibility
import Tests.Evaluate
import Tests.Let
import Tests.Unit
import Tests.UnitCase
import Tests.Boolean
import Tests.Alternatives
import Tests.SizeChange
import Tests.FirstOrder
import Tests.CoreCandidate
import Tests.Fix
import Tests.RecursiveGroup
import Tests.Diagnostic
import Tests.CheckDiagnostic
import Tests.CheckReport
import Tests.Renaming
import Tests.Substitution
import Tests.SubstitutionComposition
import Tests.Beta
import Tests.Fuel
import Tests.Declaration
import Tests.Document
import Tests.ConstructorPattern
import Tests.MotiveScope
import Tests.Manifest
import Tests.Workspace
import Tests.ProjectNew
import Tests.DataCaseParser
import Tests.DataSchema
import Tests.DataDeclaration
import Tests.Nominal
import Tests.Variant
import Tests.Box
import Tests.Sigma
import Tests.Qualified
import Tests.Rename
import Tests.Console
import Tests.ConsoleInput
import Tests.ConsoleScript
import Tests.ConsoleSequence
import Tests.Binary
import Tests.BinaryCount
import Tests.BinaryDescriptions
import Tests.CoreBytes
import Tests.ByteRanges
import Tests.UTF8Bytes
import Tests.BinaryBuffer
import Tests.String
import Tests.ConsoleArguments
import Tests.IO
import Tests.ReadLine
import Tests.ResourceScope
import Tests.HandleOwnership
import Tests.ScopedOwnership
import Tests.OwnedRead
import Tests.ResourceEmission
import Tests.Quantitative
import Tests.QuantitativeCoreTranslation
import Tests.Cubical.TypedPath
import Tests.Cubical.ReusablePath
import Tests.Cubical.OpenPath
import Tests.Cubical.RuntimeInterface
import Tests.Runtime
import Tests.Properties
import Tests.TypedProperties
import Tests.RuntimeProperties
import Data.Vect
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.PathSyntax
import Fibril.Foundation.DeMorgan.ClosedPath
import Fibril.Foundation.DeMorgan.ClosedCorePath
import Fibril.Foundation.DeMorgan.IndependentPath
import Fibril.Foundation.DeMorgan.Restriction
import Data.Fin
import Data.Maybe
import System
import Data.List

%default total

-- Small exhaustive corpus checks catch polarity/substitution mistakes.
samples : List (Interval Nat)
samples =
  let atoms = [Zero, One, Var 0, Var 1]
   in atoms ++ map Reverse atoms ++
      concatMap (\x => concatMap (\y => [Meet x y, Join x y]) atoms) atoms

replacement : Nat -> Interval Nat
replacement Z = Reverse (Var 1)
replacement (S _) = Meet (Var 0) (Var 1)

endpointSubstitutionLaw : Bool
endpointSubstitutionLaw =
  all (\term => all (\b =>
    equivalentFace
      (endpointFace (substitute replacement term) b)
      (substituteFace replacement (endpointFace term b))) (the (List Bool) [False, True])) samples

endpointDisjointLaw : Bool
endpointDisjointLaw =
  all (\term => equivalentFace
    (Conjunction (endpointFace term False) (endpointFace term True)) Bottom) samples

quantities : List Quantity
quantities = [Erased, Linear, Unrestricted]

quantityAlgebra : Bool
quantityAlgebra =
  all (\a => all (\b => all (\c =>
    add (add a b) c == add a (add b c) &&
    multiply (multiply a b) c == multiply a (multiply b c) &&
    multiply a (add b c) == add (multiply a b) (multiply a c) &&
    add a b == add b a &&
    multiply a b == multiply b a &&
    add a Erased == a &&
    multiply a Linear == a &&
    multiply a Erased == Erased) quantities) quantities) quantities

termSamples : List (Term 1)
termSamples =
  [ Variable FZ, Universe 0
  , Pi Linear (Universe 0) (Variable FZ)
  , Lambda Linear (Variable FZ) (Variable (FS FZ))
  , Apply (Variable FZ) (Universe 1)
  ]

dependentContext : Context 2
dependentContext = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)

intervalNodeCount : ScopedInterval n -> Nat
intervalNodeCount Zero = 1
intervalNodeCount One = 1
intervalNodeCount (Var _) = 1
intervalNodeCount (Reverse r) = 1 + intervalNodeCount r
intervalNodeCount (Meet r s) = 1 + intervalNodeCount r + intervalNodeCount s
intervalNodeCount (Join r s) = 1 + intervalNodeCount r + intervalNodeCount s

pathNodeCount : CorePathExpr n -> Nat
pathNodeCount (CoreTerm _) = 1
pathNodeCount (CoreAbstract body) = 1 + pathNodeCount body
pathNodeCount (CoreApply path r) = 1 + pathNodeCount path + intervalNodeCount r

sameScopedInterval : ScopedInterval n -> ScopedInterval n -> Bool
sameScopedInterval Zero Zero = True
sameScopedInterval One One = True
sameScopedInterval (Var i) (Var j) = i == j
sameScopedInterval (Reverse x) (Reverse y) = sameScopedInterval x y
sameScopedInterval (Meet x y) (Meet z w) = sameScopedInterval x z && sameScopedInterval y w
sameScopedInterval (Join x y) (Join z w) = sameScopedInterval x z && sameScopedInterval y w
sameScopedInterval _ _ = False

sameCorePath : CorePathExpr n -> CorePathExpr n -> Bool
sameCorePath (CoreTerm x) (CoreTerm y) = sameSyntax x y
sameCorePath (CoreAbstract x) (CoreAbstract y) = sameCorePath x y
sameCorePath (CoreApply p r) (CoreApply q s) =
  sameCorePath p q && sameScopedInterval r s
sameCorePath _ _ = False

boundedInstantiationCorpus : Bool
boundedInstantiationCorpus = all checkPair
  [(value, body) | value <- values, body <- bodies]
  where
    values : List (ScopedInterval 0)
    values =
      let atoms = the (List (ScopedInterval 0)) [Zero, One, Reverse Zero] in
      atoms ++ [f x y | x <- atoms, y <- atoms, f <- [Meet, Join]]

    bodies : List (CorePathExpr 1)
    bodies =
      [ CoreTerm BoolTrue
      , CoreApply (CoreTerm BoolFalse) (Var FZ)
      , CoreApply (CoreTerm BoolTrue) (Join (Var FZ) (Var FZ))
      , CoreAbstract (CoreApply (CoreTerm BoolTrue) (Meet (Var FZ) (Var (FS FZ))))
      , CoreAbstract (CoreAbstract
          (CoreApply (CoreTerm BoolFalse) (Join (Var FZ) (Var (FS (FS FZ))))))
      ]

    checkPair : (ScopedInterval 0, CorePathExpr 1) -> Bool
    checkPair (value, body) =
      let expected = instantiateCoreDimension value body
          exact = pathNodeCount expected in
      case (instantiateCoreWithin exact value body,
            instantiateCoreWithin (pred exact) value body,
            instantiateCoreWithin (S exact) value body) of
        (Just result, Nothing, Just larger) =>
          sameCorePath result expected && sameCorePath larger expected &&
          pathWithinBudget exact result && not (pathWithinBudget (pred exact) result)
        _ => False

boundedOpenInstantiationCorpus : Bool
boundedOpenInstantiationCorpus = all checkPair
  [(value, body) | value <- values, body <- bodies]
  where
    values : List (ScopedInterval 1)
    values =
      let atoms = the (List (ScopedInterval 1)) [Zero, One, Var FZ, Reverse (Var FZ)] in
      atoms ++ [f x y | x <- atoms, y <- atoms, f <- [Meet, Join]]

    bodies : List (CorePathExpr 2)
    bodies =
      [ CoreApply (CoreTerm BoolTrue) (Join (Var FZ) (Var (FS FZ)))
      , CoreAbstract (CoreApply (CoreTerm BoolFalse)
          (Join (Var (FS FZ)) (Meet (Var FZ) (Var (FS (FS FZ))))))
      , CoreAbstract (CoreAbstract (CoreApply (CoreTerm BoolTrue)
          (Join (Var (FS (FS FZ))) (Var (FS (FS (FS FZ)))))))
      ]

    checkPair : (ScopedInterval 1, CorePathExpr 2) -> Bool
    checkPair (value, body) =
      let expected = instantiateCoreDimension value body
          exact = pathNodeCount expected in
      case (instantiateCoreWithin exact value body,
            instantiateCoreWithin (pred exact) value body,
            instantiateCoreWithin (S exact) value body) of
        (Just result, Nothing, Just larger) =>
          sameCorePath result expected && sameCorePath larger expected &&
          pathWithinBudget exact result && not (pathWithinBudget (pred exact) result)
        _ => False

checks : List (String, Bool)
checks =
  [ ("bounded dimension instantiation corpus matches exact substitution and budget", boundedInstantiationCorpus)
  , ("bounded open instantiation corpus matches exact substitution and budget", boundedOpenInstantiationCorpus)
  , ("context dependent lookup shifts domain",
      sameSyntax (lookupType FZ dependentContext) (Variable (FS FZ)))
  , ("context older lookup shifts through entries",
      sameSyntax (lookupType (FS FZ) dependentContext) (Universe 0))
  , ("context quantity lookup",
      lookupQuantity FZ dependentContext == Linear &&
      lookupQuantity (FS FZ) dependentContext == Erased)
  , ("context valid runtime usage",
      case validateUsage RuntimeMode dependentContext [Linear, Erased] of
        Right () => True
        Left _ => False)
  , ("context rejects erased outer extraction",
      case validateUsage RuntimeMode dependentContext [Linear, Linear] of
        Left err => finToNat err.variable == 1 &&
                    err.mismatch.expected == Erased &&
                    err.mismatch.observed == Linear
        Right () => False)
  , ("context rejects unused linear entry",
      case validateUsage RuntimeMode dependentContext [Erased, Erased] of
        Left err => finToNat err.variable == 0
        Right () => False)
  , ("context erased mode permits type dependence",
      case validateUsage ErasedMode dependentContext [Erased, Erased] of
        Right () => True
        Left _ => False)
  , ("context erased mode checks entire vector",
      case validateUsage ErasedMode dependentContext [Erased, Linear] of
        Left err => finToNat err.variable == 1
        Right () => False)
  , ("context empty usage",
      case validateUsage RuntimeMode Empty [] of
        Right () => True
        Left _ => False)
  , ("usage variable position",
      variableUsage {n=3} RuntimeMode (FS FZ) == [Erased, Linear, Erased])
  , ("usage erased variable",
      variableUsage {n=2} ErasedMode FZ == [Erased, Erased])
  , ("usage duplicated input saturates",
      combineUsage (the (Usage 1) [Linear]) [Linear] == [Unrestricted])
  , ("usage erased scaling",
      scaleUsage Erased (the (Usage 2) [Linear, Unrestricted]) == [Erased, Erased])
  , ("usage unrestricted scaling",
      scaleUsage Unrestricted (the (Usage 2) [Erased, Linear]) == [Erased, Unrestricted])
  , ("usage linear discharge preserves outer usage",
      case discharge RuntimeMode Linear (the (Usage 2) [Linear, Unrestricted]) of
        Right rest => rest == [Unrestricted]
        Left _ => False)
  , ("usage linear discard rejected",
      case discharge RuntimeMode Linear (the (Usage 1) [Erased]) of
        Left err => err.expected == Linear && err.observed == Erased
        Right _ => False)
  , ("usage linear duplication rejected",
      case discharge RuntimeMode Linear (the (Usage 1) [Unrestricted]) of
        Left _ => True
        Right _ => False)
  , ("usage erased runtime extraction rejected",
      case discharge RuntimeMode Erased (the (Usage 1) [Linear]) of
        Left _ => True
        Right _ => False)
  , ("usage erased judgment zeros binder expectation",
      case discharge ErasedMode Linear (the (Usage 1) [Erased]) of
        Right [] => True
        Left _ => False)
  , ("usage erased judgment rejects nonzero bound use",
      case discharge ErasedMode Unrestricted (the (Usage 1) [Linear]) of
        Left _ => True
        Right _ => False)
  , ("term rename identity", all (\t => sameSyntax (rename id t) t) termSamples)
  , ("term substitution identity",
      all (\t => sameSyntax (substituteTerm Variable t) t) termSamples)
  , ("term weakening followed by instantiation",
      all (\t => sameSyntax (instantiateTerm (Universe 0) (weaken t)) t) termSamples)
  , ("term replacement avoids capture", sameSyntax
      (substituteTerm (\i => the (Term 1) (Variable FZ))
        (the (Term 1) (Lambda Linear (Universe 0) (Variable (FS FZ)))))
      (Lambda Linear (Universe 0) (Variable (FS FZ))))
  , ("term bound variable preserved", sameSyntax
      (substituteTerm (\i => the (Term 0) (Universe 2))
        (the (Term 1) (Lambda Linear (Universe 0) (Variable FZ))))
      (Lambda Linear (Universe 0) (Variable FZ)))
  , ("term domain outside binder", sameSyntax
      (instantiateTerm (the (Term 0) (Universe 2))
        (Lambda Linear (Variable FZ) (Variable FZ)))
      (Lambda Linear (Universe 2) (Variable FZ)))
  , ("term quantities differ", not (sameSyntax
      (the (Term 0) (Pi Linear (Universe 0) (Universe 0)))
      (Pi Erased (Universe 0) (Universe 0))))
  , ("term syntax equality does not reduce", not (sameSyntax
      (the (Term 0) (Apply (Lambda Linear (Universe 0) (Variable FZ)) (Universe 0)))
      (Universe 0)))
  , ("quantity semiring exhaustive laws", quantityAlgebra)
  , ("linear binder cannot discard", not (allows Linear Erased))
  , ("linear binder cannot duplicate", not (allows Linear (add Linear Linear)))
  , ("linear binder accepts exact use", allows Linear Linear)
  , ("erased binder rejects runtime use", not (allows Erased Linear))
  , ("unrestricted binder permits discard", allows Unrestricted Erased)
  , ("scoped face instantiate endpoint", entailsScoped
      STop (instantiateFace (the (ScopedInterval 0) Zero) (SEndpoint FZ False)))
  , ("scoped face instantiate opposite", entailsScoped
      (instantiateFace (the (ScopedInterval 0) Zero) (SEndpoint FZ True)) SBottom)
  , ("scoped face weakening", equivalentFace
      (forgetFace (weakenFace (the (ScopedFace 1) (SEndpoint FZ False))))
      (Endpoint 1 False))
  , ("restriction assumption available", holds
      (restrict (the (Restriction 1) unrestricted) (SEndpoint FZ False))
      (SEndpoint FZ False))
  , ("restriction does not invent assumption", not (holds
      (the (Restriction 1) unrestricted) (SEndpoint FZ False)))
  , ("restriction contradiction", isEmptyRestriction
      (restrict (restrict (the (Restriction 1) unrestricted) (SEndpoint FZ False))
                (SEndpoint FZ True)))
  , ("empty face entails arbitrary goal", holds
      (Under (the (ScopedFace 1) SBottom)) (SEndpoint FZ True))
  , ("restriction substitution", isEmptyRestriction
      (substituteRestriction (\i => the (ScopedInterval 0) One)
        (Under (the (ScopedFace 1) (SEndpoint FZ False)))))
  , ("restriction weakening keeps older assumption", holds
      (weakenRestriction (Under (the (ScopedFace 1) (SEndpoint FZ True))))
      (SEndpoint (FS FZ) True))
  , ("closed interval accepts constants", isJust (scopeInterval 0 (Meet Zero One)))
  , ("closed interval rejects variable", isNothing (scopeInterval 0 (Var 0)))
  , ("dimension boundary accepted", isJust (scopeInterval 2 (Var 1)))
  , ("dimension boundary rejected", isNothing (scopeInterval 2 (Var 2)))
  , ("reject invalid dimension even in dead meet",
      isNothing (scopeInterval 0 (Meet Zero (Var 5))))
  , ("face scope accepted", isJust (scopeFace 1 (Endpoint 0 False)))
  , ("face scope rejected", isNothing (scopeFace 1 (Endpoint 1 False)))
  , ("dead face still scope checked",
      isNothing (scopeFace 0 (Conjunction Bottom (Endpoint 0 False))))
  , ("weakening shifts index", equivalent
      (forgetInterval (weakenInterval (the (ScopedInterval 1) (Var FZ)))) (Var 1))
  , ("instantiate newest dimension", equivalent
      (forgetInterval (instantiate (the (ScopedInterval 1) One) (Var FZ))) One)
  , ("instantiate retains older dimension", equivalent
      (forgetInterval (instantiate (the (ScopedInterval 1) One) (Var (FS FZ)))) (Var 0))
  , ("core path dimension substitution composes through binders",
      let expr : CorePathExpr 1
          expr = CoreAbstract (CoreApply (CoreTerm BoolTrue) (Meet (Var FZ) (Var (FS FZ))))
          first : Fin 1 -> ScopedInterval 1
          first _ = Reverse (Var FZ)
          second : Fin 1 -> ScopedInterval 0
          second _ = One
          sequential = substituteCoreDimensions second (substituteCoreDimensions first expr)
          combined = substituteCoreDimensions (\i => substituteScoped second (first i)) expr in
      case (sequential, combined) of
        (CoreAbstract (CoreApply (CoreTerm BoolTrue) a),
         CoreAbstract (CoreApply (CoreTerm BoolTrue) b)) =>
           equivalent (forgetInterval a) (forgetInterval b)
        _ => False)
  , ("core path substitution avoids dimension capture",
      case instantiateCoreDimension (the (ScopedInterval 1) (Var FZ))
             (CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var (FS FZ)))) of
        CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var (FS FZ))) => True
        _ => False)
  , ("core path substitution preserves bound dimension",
      case instantiateCoreDimension (the (ScopedInterval 0) One)
             (CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var FZ))) of
        CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var FZ)) => True
        _ => False)
  , ("core path substitution replaces free dimension",
      case instantiateCoreDimension (the (ScopedInterval 0) One)
             (CoreApply (CoreTerm BoolTrue) (Var FZ)) of
        CoreApply (CoreTerm BoolTrue) One => True
        _ => False)
  , ("closed core path checks after dimension weakening",
      case checkCorePathExpr 64 64 3
             (substituteCoreDimensions (Var . FS)
               (the (CorePathExpr 0) (CoreAbstract (CoreTerm BoolTrue))))
             BoolTrue BoolTrue of
        Accepted => True; _ => False)
  , ("open core path rejects unsupported dimension-dependent body",
      case checkCorePathExpr 64 64 3
             (the (CorePathExpr 1) (CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var FZ))))
             BoolTrue BoolTrue of
        Rejected => True; _ => False)
  , ("constant core path applies at open dimension",
      case applyCorePathAt 64 64 4 (the (CorePathExpr 1) (CoreAbstract (CoreTerm BoolTrue)))
             (Var FZ) BoolTrue BoolTrue of
        CoreStepped (CoreTerm BoolTrue) => True; _ => False)
  , ("constant core path applies at open compound interval",
      case applyCorePathAt 64 64 4 (the (CorePathExpr 1) (CoreAbstract (CoreTerm BoolFalse)))
             (Meet (Var FZ) (Reverse (Var FZ))) BoolFalse BoolFalse of
        CoreStepped (CoreTerm BoolFalse) => True; _ => False)
  , ("open path application rejects bad boundary",
      case applyCorePathAt 64 64 4 (the (CorePathExpr 1) (CoreAbstract (CoreTerm BoolTrue)))
             (Var FZ) BoolTrue BoolFalse of
        CoreStepRejected => True; _ => False)
  , ("open path application budget exhaustion",
      case applyCorePathAt 64 64 3 (the (CorePathExpr 1) (CoreAbstract (CoreTerm BoolTrue)))
             (Var FZ) BoolTrue BoolTrue of
        CoreStepExhausted => True; _ => False)
  , ("nested beta commutes with endpoint substitution",
      let path : CorePathExpr 1
          path = CoreAbstract (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))
          closed : Fin 1 -> ScopedInterval 0
          closed _ = One in
      case (applyCorePathAt 64 64 5 path (Reverse (Var FZ)) BoolTrue BoolTrue,
            applyCorePathAt 64 64 5 (substituteCoreDimensions closed path)
              (substituteScoped closed (Reverse (Var FZ))) BoolTrue BoolTrue) of
        (CoreStepped result, CoreStepped expected) =>
          case (substituteCoreDimensions closed result, expected) of
            (CoreApply (CoreAbstract (CoreTerm BoolTrue)) a,
             CoreApply (CoreAbstract (CoreTerm BoolTrue)) b) =>
               equivalent (forgetInterval a) (forgetInterval b)
            _ => False
        _ => False)
  , ("dimension substitution output admits exact node budget",
      case instantiateCoreWithin 3 (the (ScopedInterval 1) (Var FZ))
             (CoreApply (CoreTerm BoolTrue) (Var FZ)) of
        Just (CoreApply (CoreTerm BoolTrue) (Var FZ)) => True; _ => False)
  , ("dimension substitution output charges duplicated interval",
      case instantiateCoreWithin 8
             (the (ScopedInterval 1) (Meet (Var FZ) (Join One Zero)))
             (CoreApply (CoreTerm BoolTrue) (Join (Var FZ) (Var FZ))) of
        Nothing => True; _ => False)
  , ("checked open application rejects oversized substituted result",
      case applyCorePathAt 8 64 6
             (the (CorePathExpr 1) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Join (Var FZ) (Var FZ)))))
             (Meet (Var FZ) (Join One Zero)) BoolTrue BoolTrue of
        CoreStepExhausted => True; _ => False)
  , ("open application interval node budget exhaustion",
      case applyCorePathAt 4 64 5
             (the (CorePathExpr 1) (CoreAbstract (CoreTerm BoolTrue)))
             (Meet (Meet (Var FZ) One) (Join (Var FZ) Zero)) BoolTrue BoolTrue of
        CoreStepExhausted => True; _ => False)
  , ("path and interval nodes share admission budget",
      case checkCorePathExpr 4 64 8
             (the (CorePathExpr 0) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Meet (Var FZ) One))))
             BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("nested beta preserves open dimension",
      case applyCorePathAt 64 64 5
             (the (CorePathExpr 1) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))))
             (Reverse (Var FZ)) BoolTrue BoolTrue of
        CoreStepped (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Reverse (Var FZ))) => True
        _ => False)
  , ("nested beta rejects malformed inner path",
      case applyCorePathAt 64 64 5
             (the (CorePathExpr 1) (CoreAbstract (CoreApply (CoreTerm BoolTrue) (Var FZ))))
             (Var FZ) BoolTrue BoolTrue of
        CoreStepRejected => True; _ => False)
  , ("nested constant path checks with bound dimension",
      case checkCorePathExpr 64 64 4
             (the (CorePathExpr 0) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))))
             BoolTrue BoolTrue of
        Accepted => True; _ => False)
  , ("nested path both boundaries reduce to checked body",
      let path : CorePathExpr 0
          path = CoreAbstract (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ)) in
      case (runCorePathExpr 64 64 5 (CoreApply path Zero) BoolTrue BoolTrue,
            runCorePathExpr 64 64 5 (CoreApply path One) BoolTrue BoolTrue) of
        (CoreValue BoolTrue, CoreValue BoolTrue) => True; _ => False)
  , ("nested path face comparison exhaustion rejects checking",
      case checkCorePathExpr 64 0 4
             (the (CorePathExpr 0) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))))
             (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue of
        Exhausted => True; _ => False)
  , ("nested constant path endpoint reduces",
      case runCorePathExpr 64 64 5
             (CoreApply (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))) One)
             BoolTrue BoolTrue of
        CoreValue BoolTrue => True; _ => False)
  , ("nested constant path rejects mismatched boundary",
      case checkCorePathExpr 64 64 4
             (the (CorePathExpr 0) (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))))
             BoolTrue BoolFalse of
        Rejected => True; _ => False)
  , ("nested path body traversal exhausts independently",
      case checkCorePathExpr 64 64 3
             (the (CorePathExpr 0) (CoreAbstract (CoreApply (CoreAbstract
               (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))) (Var FZ))))
             BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("checked path milestone forms checks and checks both endpoint results",
      let body = BoolCase BoolTrue BoolFalse BoolTrue in
      case formClosedBoolPath 64 64 5 BoolFalse BoolFalse of
        Right ty => case checkPathAgainstType 64 64 5 (CoreAbstract (CoreTerm body)) ty of
          Right path => case (checkPathEndpoint 64 64 6 path False,
                              checkPathEndpoint 64 64 6 path True) of
            (Right zero, Right one) =>
              case (betaCompare 64 (forgetCheckedClosedBool zero) BoolFalse,
                    betaCompare 64 (forgetCheckedClosedBool one) BoolFalse) of
                (EqualNormalForms, EqualNormalForms) => True
                _ => False
            _ => False
          Left _ => False
        Left _ => False)
  , ("closed path endpoint also passes ordinary runtime checking",
      case formClosedBoolPath 64 64 5 BoolTrue BoolTrue of
        Right ty => case checkPathAgainstType 64 64 5 (CoreAbstract (CoreTerm BoolTrue)) ty of
          Right path => case (checkRuntimePathEndpoint 64 64 6 path False,
                              checkRuntimePathEndpoint 64 64 6 path True) of
            (Right _, Right _) => True; _ => False
          Left _ => False
        Left _ => False)
  , ("raw closed path lowering checks both endpoint observations",
      let path = CoreAbstract (CoreTerm (BoolCase BoolTrue BoolFalse BoolTrue)) in
      case (lowerClosedBoolEndpoint 64 64 6 path BoolFalse BoolFalse False,
            lowerClosedBoolEndpoint 64 64 6 path BoolFalse BoolFalse True) of
        (Right zero, Right one) =>
          case (betaCompare 64 (forgetRuntimeCheckedBool zero) BoolFalse,
                betaCompare 64 (forgetRuntimeCheckedBool one) BoolFalse) of
            (EqualNormalForms, EqualNormalForms) => True
            _ => False
        _ => False)
  , ("raw lowering rejects mismatched unobserved boundaries",
      let path = CoreAbstract (CoreTerm BoolTrue) in
      case (lowerClosedBoolEndpoint 64 64 6 path BoolTrue BoolFalse False,
            lowerClosedBoolEndpoint 64 64 6 path BoolFalse BoolTrue True) of
        (Left ClosedPathRejected, Left ClosedPathRejected) => True
        _ => False)
  , ("raw lowering fails closed on unsupported payload and exhaustion",
      case (lowerClosedBoolEndpoint 64 64 6 (CoreAbstract (CoreTerm UnitValue)) BoolTrue BoolTrue False,
            lowerClosedBoolEndpoint 0 64 6 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue False,
            lowerClosedBoolEndpoint 64 0 6
              (CoreAbstract (CoreTerm (BoolCase BoolTrue BoolTrue BoolFalse))) BoolTrue BoolTrue False,
            lowerClosedBoolEndpoint 64 64 0 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue False) of
        (Left ClosedPathRejected, Left ClosedPathExhausted,
         Left ClosedPathExhausted, Left ClosedPathExhausted) => True
        _ => False)
  , ("runtime checked endpoint composes with ordinary linear identity",
      case checkClosedPath 64 64 5 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Right path => case checkRuntimePathEndpoint 64 64 6 path False of
          Right value =>
            let program = Apply (Lambda Linear BoolType (Variable FZ)) (forgetRuntimeCheckedBool value) in
            case (checkRuntime 64 64 Empty program BoolType, normalize 64 program) of
              (Right _, Normal BoolTrue) => True; _ => False
          Left _ => False
        Left _ => False)
  , ("closed runtime endpoint propagates exhaustion",
      case formClosedBoolPath 64 64 5 BoolTrue BoolTrue of
        Right ty => case checkPathAgainstType 64 64 5 (CoreAbstract (CoreTerm BoolTrue)) ty of
          Right path => case checkRuntimePathEndpoint 0 64 6 path False of
            Left ClosedPathExhausted => True; _ => False
          Left _ => False
        Left _ => False)
  , ("checked endpoint rejects budget exhaustion",
      case formClosedBoolPath 64 64 5 BoolTrue BoolTrue of
        Right ty => case checkPathAgainstType 64 64 5 (CoreAbstract (CoreTerm BoolTrue)) ty of
          Right path => case checkPathEndpoint 64 64 1 path False of
            Left ClosedPathExhausted => True; _ => False
          Left _ => False
        Left _ => False)
  , ("closed Bool path type forms and checks before application",
      case formClosedBoolPath 64 64 4 BoolTrue BoolTrue of
        Right ty => case checkPathAgainstType 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) ty of
          Right path => case (applyCheckedClosedPath 64 64 5 path Zero,
                              applyCheckedClosedPath 64 64 5 path One) of
            (CoreValue BoolTrue, CoreValue BoolTrue) => True
            _ => False
          Left _ => False
        Left _ => False)
  , ("distinct Bool endpoints form but do not invent a path",
      case formClosedBoolPath 64 64 4 BoolTrue BoolFalse of
        Right ty => case checkPathAgainstType 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) ty of
          Left ClosedPathRejected => True; _ => False
        Left _ => False)
  , ("closed Bool path formation rejects non-Boolean endpoints",
      case formClosedBoolPath 64 64 4 BoolTrue UnitValue of
        Left ClosedPathRejected => True; _ => False)
  , ("closed Bool path formation propagates exhaustion",
      case formClosedBoolPath 64 64 2 BoolTrue BoolTrue of
        Left ClosedPathExhausted => True; _ => False)
  , ("independent closed path witness applies at both endpoints",
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Right path => case (applyCheckedClosedPath 64 64 5 path Zero,
                            applyCheckedClosedPath 64 64 5 path One) of
          (CoreValue BoolTrue, CoreValue BoolTrue) => True
          _ => False
        Left _ => False)
  , ("checked closed path applies at open dimension",
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Right path => case applyCheckedPathAt 64 64 5 path (the (ScopedInterval 1) (Var FZ)) of
          CoreStepped (CoreTerm BoolTrue) => True; _ => False
        Left _ => False)
  , ("checked nested path substitutes an open dimension",
      case checkClosedPath 64 64 4
             (CoreAbstract (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))) BoolTrue BoolTrue of
        Right path => case applyCheckedPathAt 64 64 5 path (the (ScopedInterval 1) (Reverse (Var FZ))) of
          CoreStepped (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Reverse (Var FZ))) => True
          _ => False
        Left _ => False)
  , ("checked path weakening respects new syntax budget",
      case checkClosedPath 64 64 4
             (CoreAbstract (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ))) BoolTrue BoolTrue of
        Right path => case applyCheckedPathAt 2 64 5 path (the (ScopedInterval 1) (Var FZ)) of
          CoreStepExhausted => True; _ => False
        Left _ => False)
  , ("checked path open application can exhaust",
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Right path => case applyCheckedPathAt 64 64 1 path (the (ScopedInterval 1) (Var FZ)) of
          CoreStepExhausted => True; _ => False
        Left _ => False)
  , ("independent path endpoint result remains core typed and converts to boundary",
      let body = BoolCase BoolTrue BoolFalse BoolTrue in
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm body)) BoolFalse BoolFalse of
        Right path => case applyCheckedClosedPath 64 64 5 path One of
          CoreValue result => case (checkErased 64 64 Empty result BoolType,
                                    betaCompare 64 result BoolFalse) of
            (Right _, EqualNormalForms) => True
            _ => False
          _ => False
        Left _ => False)
  , ("independent path never accepts unsupported core syntax in dead branch",
      case checkClosedPath 64 64 4
             (CoreAbstract (CoreTerm (BoolCase BoolTrue BoolTrue UnitValue))) BoolTrue BoolTrue of
        Left ClosedPathRejected => True; _ => False)
  , ("independent closed path rejects boundary mismatch",
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolFalse of
        Left ClosedPathRejected => True; _ => False)
  , ("independent closed path propagates exhausted checking",
      case checkClosedPath 64 64 1 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Left ClosedPathExhausted => True; _ => False)
  , ("independent witness application can exhaust",
      case checkClosedPath 64 64 4 (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue of
        Right path => case applyCheckedClosedPath 64 64 1 path Zero of
          CoreExhausted => True; _ => False
        Left _ => False)
  , ("raw core path abstraction checks",
      case checkCorePathExpr 64 64 3 (the (CorePathExpr 0) (CoreAbstract (CoreTerm BoolTrue))) BoolTrue BoolTrue of
        Accepted => True; _ => False)
  , ("raw core path endpoints reduce",
      case (runCorePathExpr 64 64 4 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) Zero) BoolTrue BoolTrue,
            runCorePathExpr 64 64 4 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) One) BoolTrue BoolTrue) of
        (CoreValue BoolTrue, CoreValue BoolTrue) => True; _ => False)
  , ("raw core path rejects wrong left face",
      case checkCorePathExpr 64 64 4
             (the (CorePathExpr 0) (CoreAbstract (CoreTerm BoolTrue))) BoolFalse BoolTrue of
        Rejected => True; _ => False)
  , ("raw core path rejects wrong right face",
      case checkCorePathExpr 64 64 4
             (the (CorePathExpr 0) (CoreAbstract (CoreTerm BoolTrue))) BoolTrue BoolFalse of
        Rejected => True; _ => False)
  , ("raw core path checks convertible endpoint terms",
      case checkCorePathExpr 64 64 4
             (the (CorePathExpr 0) (CoreAbstract (CoreTerm BoolTrue)))
             (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue of
        Accepted => True; _ => False)
  , ("raw core path rejects boundary mismatch",
      case runCorePathExpr 64 64 4 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) One) BoolTrue BoolFalse of
        CoreRejected => True; _ => False)
  , ("raw core path reduces compound closed interval",
      case runCorePathExpr 64 64 5 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Reverse (Meet One Zero))) BoolTrue BoolTrue of
        CoreValue BoolTrue => True; _ => False)
  , ("raw core path closed interval depth exhaustion",
      case runCorePathExpr 64 64 4 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Reverse (Reverse (Reverse Zero)))) BoolTrue BoolTrue of
        CoreExhausted => True; _ => False)
  , ("raw core path rejects non-path application",
      case runCorePathExpr 64 64 4 (CoreApply (CoreTerm BoolTrue) Zero) BoolTrue BoolTrue of
        CoreRejected => True; _ => False)
  , ("raw core endpoint propagates exhaustion",
      case runCorePathExpr 64 64 3 (CoreApply (CoreAbstract (CoreTerm BoolTrue)) Zero) BoolTrue BoolTrue of
        CoreExhausted => True; _ => False)
  , ("core literal constant path checks", case checkClosedCorePath 64 64 3 BoolTrue BoolTrue BoolTrue of
        Accepted => True; _ => False)
  , ("core constant path both endpoints compute",
      case (applyClosedCoreEndpoint 64 64 3 False BoolTrue BoolTrue BoolTrue,
            applyClosedCoreEndpoint 64 64 3 True BoolTrue BoolTrue BoolTrue) of
        (CoreValue BoolTrue, CoreValue BoolTrue) => True; _ => False)
  , ("core endpoint rejects mismatch", case applyClosedCoreEndpoint 64 64 3 False BoolTrue BoolTrue BoolFalse of
        CoreRejected => True; _ => False)
  , ("core literal path rejects mismatch", case checkClosedCorePath 64 64 3 BoolTrue BoolTrue BoolFalse of
        Rejected => True; _ => False)
  , ("core path rejects wrong type", case checkClosedCorePath 64 64 3 UnitValue BoolTrue BoolTrue of
        Rejected => True; _ => False)
  , ("core path compares both reducible boundaries",
      case checkClosedCorePath 64 64 3
             (BoolCase BoolTrue BoolFalse BoolTrue)
             (BoolCase BoolFalse BoolTrue BoolFalse)
             (BoolCase BoolTrue BoolFalse BoolTrue) of
        Accepted => True; _ => False)
  , ("core path rejects different reducible boundary",
      case checkClosedCorePath 64 64 3 BoolTrue BoolTrue
             (BoolCase BoolFalse BoolTrue BoolFalse) of
        Rejected => True; _ => False)
  , ("core path compares reduced boolean expressions",
      case checkClosedCorePath 64 64 3 (BoolCase BoolTrue BoolFalse BoolTrue) BoolFalse BoolFalse of
        Accepted => True; _ => False)
  , ("core path rejects unsupported dead branch",
      case checkClosedCorePath 64 64 3 (BoolCase BoolTrue BoolTrue UnitValue) BoolTrue BoolTrue of
        Rejected => True; _ => False)
  , ("core Boolean admission budget spans all three inputs",
      case checkClosedCorePath 5 64 3
             (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("core Boolean admission accepts exact node budget",
      case checkClosedCorePath 6 64 3
             (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue BoolTrue of
        Accepted => True; _ => False)
  , ("core Boolean grammar shares node budget across branches",
      case checkClosedCorePath 4 64 3
             (BoolCase BoolTrue (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue)
             BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("core Boolean grammar depth exhaustion",
      case checkClosedCorePath 2 64 3
             (BoolCase BoolTrue (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue)
             BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("core Boolean grammar rejects unsupported deep dead branch",
      case checkClosedCorePath 64 64 3
             (BoolCase BoolTrue BoolTrue (BoolCase BoolTrue BoolTrue UnitValue))
             BoolTrue BoolTrue of
        Rejected => True; _ => False)
  , ("core boolean reduction budget exhaustion",
      case checkClosedCorePath 64 0 3 (BoolCase BoolTrue BoolTrue BoolFalse) BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("core path rejects nonliteral", case checkClosedCorePath 64 64 3 BoolType BoolTrue BoolTrue of
        Rejected => True; _ => False)
  , ("core path propagates checker exhaustion", case checkClosedCorePath 0 64 3 BoolTrue BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("core path propagates path exhaustion", case checkClosedCorePath 64 64 2 BoolTrue BoolTrue BoolTrue of
        Exhausted => True; _ => False)
  , ("closed constant path checks", case checkConstantPath 3 (Abstract (Literal True)) True True of
        Accepted => True; _ => False)
  , ("closed path rejects mismatched endpoint", case checkConstantPath 3 (Abstract (Literal True)) True False of
        Rejected => True; _ => False)
  , ("closed path rejects non-boolean body", case checkConstantPath 3 (Abstract (Abstract (Literal True))) True True of
        Rejected => True; _ => False)
  , ("closed path budget exhaustion", case checkConstantPath 2 (Abstract (Literal True)) True True of
        Exhausted => True; _ => False)
  , ("closed path zero endpoint", case runEndpoint 4 (Apply (Abstract (Literal True)) Zero) True True of
        EndpointValue True => True; _ => False)
  , ("closed path one endpoint", case runEndpoint 4 (Apply (Abstract (Literal False)) One) False False of
        EndpointValue False => True; _ => False)
  , ("endpoint rejects mismatched boundary", case runEndpoint 4 (Apply (Abstract (Literal True)) One) True False of
        InvalidEndpoint => True; _ => False)
  , ("endpoint budget exhaustion", case runEndpoint 3 (Apply (Abstract (Literal True)) Zero) True True of
        EndpointExhausted => True; _ => False)
  , ("endpoint rejects unsupported interval", case runEndpoint 4 (Apply (Abstract (Literal True)) (Reverse Zero)) True True of
        InvalidEndpoint => True; _ => False)
  , ("path dimension substitution avoids capture",
      case instantiateDimension (the (ScopedInterval 1) (Var FZ))
             (Abstract (Apply (Literal True) (Var (FS FZ)))) of
        Abstract (Apply (Literal True) (Var (FS FZ))) => True
        _ => False)
  , ("path dimension substitution preserves bound dimension",
      case instantiateDimension (the (ScopedInterval 0) One)
             (Abstract (Apply (Literal True) (Var FZ))) of
        Abstract (Apply (Literal True) (Var FZ)) => True
        _ => False)
  , ("path dimension substitution replaces free dimension",
      case instantiateDimension (the (ScopedInterval 0) One)
             (Apply (Literal True) (Var FZ)) of
        Apply (Literal True) One => True
        _ => False)
  , ("scoped face entailment", entailsScoped
      (SConjunction (the (ScopedFace 1) (SEndpoint FZ False)) STop)
      (SEndpoint FZ False))
  , ("endpoint substitution corpus", endpointSubstitutionLaw)
  , ("endpoint disjointness corpus", endpointDisjointLaw)
  , ("endpoint of zero", equivalentFace (endpointFace Zero False) Top)
  , ("endpoint of one", equivalentFace (endpointFace One False) Bottom)
  , ("meet zero face", equivalentFace (endpointFace (Meet (Var 0) (Var 1)) False)
      (Disjunction (Endpoint 0 False) (Endpoint 1 False)))
  , ("join one face", equivalentFace (endpointFace (Join (Var 0) (Var 1)) True)
      (Disjunction (Endpoint 0 True) (Endpoint 1 True)))
  , ("reverse swaps endpoints", equivalentFace (endpointFace (Reverse (Var 0)) False)
      (Endpoint 0 True))
  , ("face identity substitution", equivalentFace
      (substituteFace Var (Conjunction (Endpoint 0 False) (Endpoint 1 True)))
      (Conjunction (Endpoint 0 False) (Endpoint 1 True)))
  , ("face endpoint substitution", equivalentFace
      (substituteFace (const Zero) (Endpoint 0 False)) Top)
  , ("face compound substitution", equivalentFace
      (substituteFace (\n => Meet (Var n) (Var 2)) (Endpoint 0 True))
      (Conjunction (Endpoint 0 True) (Endpoint 2 True)))
  , ("substitution preserves contradiction", equivalentFace
      (substituteFace (const (Join (Var 0) (Var 1)))
        (Conjunction (Endpoint 0 False) (Endpoint 0 True))) Bottom)
  , ("boundary excluded middle still not top", not (equivalentFace
      (endpointFace (Join (Var 0) (Reverse (Var 0))) True) Top))
  , ("face contradiction", equivalentFace
      (Conjunction (Endpoint 0 False) (Endpoint 0 True)) Bottom)
  , ("face endpoints not exhaustive", not (equivalentFace
      (Disjunction (Endpoint 0 False) (Endpoint 0 True)) Top))
  , ("face conjunction entails factor", entails
      (Conjunction (Endpoint 0 False) (Endpoint 1 True)) (Endpoint 0 False))
  , ("face disjunction not entails factor", not (entails
      (Disjunction (Endpoint 0 False) (Endpoint 1 True)) (Endpoint 0 False)))
  , ("face bottom entails anything", entails Bottom (Endpoint 0 False))
  , ("face top not entails endpoint", not (entails Top (Endpoint 0 False)))
  , ("face absorption", equivalentFace
      (Disjunction (Endpoint 0 False)
        (Conjunction (Endpoint 0 False) (Endpoint 1 True))) (Endpoint 0 False))
  , ("face distribution", equivalentFace
      (Conjunction (Endpoint 0 False) (Disjunction (Endpoint 1 False) (Endpoint 2 True)))
      (Disjunction (Conjunction (Endpoint 0 False) (Endpoint 1 False))
                   (Conjunction (Endpoint 0 False) (Endpoint 2 True))))
  , ("face inconsistent branch eliminated", equivalentFace
      (Disjunction (Conjunction (Endpoint 0 False) (Endpoint 0 True))
                   (Endpoint 1 True)) (Endpoint 1 True))
  , ("face distinct dimensions", not (entails (Endpoint 0 False) (Endpoint 1 False)))
  , ("symbolic involution", equivalent (Reverse (Reverse (Var 0))) (Var 0))
  , ("symbolic De Morgan", equivalent (Reverse (Meet (Var 0) (Var 1)))
      (Join (Reverse (Var 0)) (Reverse (Var 1))))
  , ("symbolic absorption", equivalent (Join (Var 0) (Meet (Var 0) (Var 1))) (Var 0))
  , ("symbolic distribution", equivalent (Meet (Var 0) (Join (Var 1) (Var 2)))
      (Join (Meet (Var 0) (Var 1)) (Meet (Var 0) (Var 2))))
  , ("symbolic commutativity", equivalent (Meet (Var 0) (Var 1)) (Meet (Var 1) (Var 0)))
  , ("symbolic idempotence", equivalent (Join (Var 0) (Var 0)) (Var 0))
  , ("symbolic bounds", equivalent (Meet (Var 0) One) (Join Zero (Var 0)))
  , ("no excluded middle", not (equivalent (Join (Var 0) (Reverse (Var 0))) One))
  , ("no complement cancellation", not (equivalent (Meet (Var 0) (Reverse (Var 0))) Zero))
  , ("distinct generators", not (equivalent (Var 0) (Var 1)))
  , ("erased notation", show Erased == "0")
  , ("linear notation", show Linear == "1")
  , ("unrestricted notation", show Unrestricted == "unrestricted")
  , ("distinct quantities", not (Erased == Linear) && not (Linear == Unrestricted))
  , ("zero endpoint", not (atVertex (const False) (the (Interval Nat) Zero)))
  , ("one endpoint", atVertex (const False) (the (Interval Nat) One))
  , ("variable endpoint", atVertex (const True) (Var Z))
  , ("reversal endpoint", not (atVertex (const True) (Reverse (Var Z))))
  , ("meet endpoints", not (atVertex (const True) (Meet (Var Z) Zero)))
  , ("join endpoints", atVertex (const False) (Join (Var Z) One))
  , ("substitution at endpoint",
      atVertex (const False)
        (substitute (\n => the (Interval Nat) One) (Var Z)))
  , ("substitution under reversal",
      not (atVertex (const False)
        (substitute (\n => the (Interval Nat) One) (Reverse (Var Z)))))
  , ("double reversal",
      atVertex (const True) (Reverse (Reverse (Var Z))))
  , ("De Morgan at endpoint",
      atVertex (const False) (Reverse (Meet (Var Z) One)) ==
      atVertex (const False) (Join (Reverse (Var Z)) (Reverse One)))
  ]

main : IO ()
main = do
  sequenceChecks <- runSequenceChecks
  binaryDescriptionChecks <- Tests.BinaryDescriptions.runBinaryDescriptionChecks
  binaryChecks <- Tests.Binary.runChecks
  bufferChecks <- Tests.BinaryBuffer.runBufferChecks
  scriptHostChecks <- runScriptHostChecks
  resourceChecks <- runResourceChecks
  projectChecks <- runProjectChecks
  let failed = filter (not . snd) (Tests.Cubical.CommonEqualityAdmission.checks ++ Tests.Cubical.CommonAdmission.checks ++ Tests.Main.checks ++ Tests.Shadow.checks ++ Tests.Quantitative.checks ++ Tests.QuantitativeCoreTranslation.checks ++ Tests.Cubical.TypedPath.checkerChecks ++ Tests.Cubical.RuntimeInterface.checks ++ Tests.Cubical.ReusablePath.checks ++ Tests.Cubical.OpenPath.checks ++ Tests.Reduction.checks ++ Tests.Erased.checks ++ Tests.Runtime.checks ++ Tests.Pretty.checks ++ Tests.SourceText.checks ++ Tests.UTF8.checks ++ Tests.Lexer.checks ++ Tests.Frontend.checks ++ Tests.Compatibility.checks ++ Tests.Evaluate.checks ++ Tests.Let.checks ++ Tests.Unit.checks ++ Tests.UnitCase.checks ++ Tests.Boolean.checks ++ Tests.Alternatives.checks ++ Tests.SizeChange.checks ++ Tests.FirstOrder.checks ++ Tests.CoreCandidate.checks ++ Tests.Fix.checks ++ Tests.RecursiveGroup.checks ++ Tests.Diagnostic.checks ++ Tests.CheckDiagnostic.checks ++ Tests.CheckReport.checks ++ Tests.Renaming.checks ++ Tests.Substitution.checks ++ Tests.SubstitutionComposition.checks ++ Tests.Beta.checks ++ Tests.Fuel.checks ++ Tests.Declaration.checks ++ Tests.Document.checks ++ Tests.ConstructorPattern.checks ++ Tests.MotiveScope.checks ++ Tests.Manifest.checks ++ Tests.Workspace.checks ++ Tests.DataCaseParser.checks ++ Tests.DataSchema.checks ++ Tests.DataDeclaration.checks ++ Tests.Nominal.checks ++ Tests.Variant.checks ++ Tests.Box.checks ++ Tests.Sigma.checks ++ Tests.Qualified.checks ++ Tests.Rename.checks ++ Tests.Console.checks ++ Tests.ConsoleSequence.checks ++ Tests.ConsoleScript.checks ++ Tests.ConsoleInput.checks ++ Tests.String.checks ++ Tests.ConsoleArguments.checks ++ Tests.IO.checks ++ Tests.ReadLine.checks ++ Tests.HandleOwnership.checks ++ Tests.ScopedOwnership.checks ++ Tests.OwnedRead.checks ++ Tests.ResourceEmission.checks ++ Tests.Binary.checks ++ Tests.CoreBytes.checks ++ Tests.ByteRanges.checks ++ Tests.UTF8Bytes.checks ++ Tests.BinaryCount.checks ++ Tests.BinaryDescriptions.checks ++ binaryDescriptionChecks ++ binaryChecks ++ bufferChecks ++ sequenceChecks ++ scriptHostChecks ++ resourceChecks ++ projectChecks)
  case failed of
    [] => do
      putStrLn "Deterministic bootstrap regressions passed."
      ok <- runProperties
      if ok
         then do
           typedOk <- runTypedProperties
           if typedOk
              then do
                runtimeOk <- runRuntimeProperties
                if runtimeOk then pure () else exitFailure
              else exitFailure
         else exitFailure
    _ => do
      traverse_ (putStrLn . fst) failed
      exitFailure
