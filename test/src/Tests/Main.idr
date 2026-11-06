module Tests.Main

import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Usage
import Fibril.Core.Context
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
import Tests.Runtime
import Tests.Properties
import Tests.TypedProperties
import Tests.RuntimeProperties
import Data.Vect
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Scope
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

checks : List (String, Bool)
checks =
  [ ("context dependent lookup shifts domain",
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
  binaryChecks <- Tests.Binary.runChecks
  bufferChecks <- Tests.BinaryBuffer.runBufferChecks
  scriptHostChecks <- runScriptHostChecks
  resourceChecks <- runResourceChecks
  projectChecks <- runProjectChecks
  let failed = filter (not . snd) (Tests.Main.checks ++ Tests.Reduction.checks ++ Tests.Erased.checks ++ Tests.Runtime.checks ++ Tests.Pretty.checks ++ Tests.SourceText.checks ++ Tests.UTF8.checks ++ Tests.Lexer.checks ++ Tests.Frontend.checks ++ Tests.Compatibility.checks ++ Tests.Evaluate.checks ++ Tests.Let.checks ++ Tests.Unit.checks ++ Tests.UnitCase.checks ++ Tests.Boolean.checks ++ Tests.Alternatives.checks ++ Tests.Diagnostic.checks ++ Tests.CheckDiagnostic.checks ++ Tests.CheckReport.checks ++ Tests.Renaming.checks ++ Tests.Substitution.checks ++ Tests.SubstitutionComposition.checks ++ Tests.Beta.checks ++ Tests.Fuel.checks ++ Tests.Declaration.checks ++ Tests.Document.checks ++ Tests.ConstructorPattern.checks ++ Tests.MotiveScope.checks ++ Tests.Manifest.checks ++ Tests.Workspace.checks ++ Tests.DataCaseParser.checks ++ Tests.DataSchema.checks ++ Tests.DataDeclaration.checks ++ Tests.Nominal.checks ++ Tests.Variant.checks ++ Tests.Box.checks ++ Tests.Sigma.checks ++ Tests.Qualified.checks ++ Tests.Rename.checks ++ Tests.Console.checks ++ Tests.ConsoleSequence.checks ++ Tests.ConsoleScript.checks ++ Tests.ConsoleInput.checks ++ Tests.String.checks ++ Tests.ConsoleArguments.checks ++ Tests.IO.checks ++ Tests.ReadLine.checks ++ Tests.HandleOwnership.checks ++ Tests.ScopedOwnership.checks ++ Tests.OwnedRead.checks ++ Tests.ResourceEmission.checks ++ Tests.Binary.checks ++ binaryChecks ++ bufferChecks ++ sequenceChecks ++ scriptHostChecks ++ resourceChecks ++ projectChecks)
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
