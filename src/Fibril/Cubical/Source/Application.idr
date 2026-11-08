module Fibril.Cubical.Source.Application

import Data.List
import Data.Maybe
import Data.Fin
import Data.Vect
import Decidable.Equality
import Fibril.Core.Term as C
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Quantitative.Syntax as Q
import Fibril.Core.Quantitative.CoreTranslation
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Source.PureDefinition
import Fibril.Cubical.Source.BoolCases
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Source.Syntax
import Fibril.Source.Global
import Fibril.Source.Lexer
import Fibril.Source.Text
import Fibril.Source.Declaration
import Fibril.Source.Document
import Fibril.Source.Navigation
import Fibril.Elaboration.Declaration
import Fibril.Elaboration.Expression
import Fibril.Driver.Limits

%default total

failAt : Declaration -> String -> Either ElaborationError a
failAt decl message = Left (ElaborationFailure decl.nameSpan.start ("Cubical guard: " ++ message))

public export
executableDeclarations : List Declaration -> List Declaration
executableDeclarations = filter (isNothing . cubicalProof)

record CheckedPureDefinition where
  constructor CheckedDefinition
  rawType : C.Term 0
  rawValue : C.Term 0
  image : PureImage [] rawValue
  exactType : coreType image.ty = rawType
  usage : Uses image.pureTerm []

checkDefinition : Declaration -> Either ElaborationError CheckedPureDefinition
checkDefinition decl = do
  if decl.quantity /= Unrestricted || decl.generated || decl.dictionary
    then failAt decl "endpoints must be unrestricted ordinary definitions" else Right ()
  ty <- case elaborateClosedWith [] decl.expected of
    Left _ => failAt decl "endpoint type is not closed in the supported pure fragment"
    Right ty => Right ty
  value <- case elaborateExpected [] Empty [] ty decl.value of
    Left _ => failAt decl "endpoint body must be closed; globals and recursion are unsupported"
    Right value => Right value
  -- The original complete source is still checked by inferRuntime after this gate.
  case inferRuntime checkingDepth typeReductionFuel Empty (Apply (Lambda Linear ty (Variable FZ)) value) of
    Left err => failAt decl ("endpoint runtime checking failed: " ++ show err)
    Right _ => Right ()
  case (readPureType 64 ty, extractPure 64 [] value) of
    (Just (a ** typeExact), Just image) => case samePureType image.ty a of
      Nothing => failAt decl "endpoint declared type disagrees with its exact pure image"
      Just Refl => case pureUses image.pureTerm of
        Nothing => failAt decl "endpoint has no valid quantitative Uses derivation"
        Just ([] ** usage) => Right (CheckedDefinition ty value image typeExact usage)
    _ => failAt decl "unsupported endpoint (only total pure Unit/Bool/arrows and their constructors/eliminators)"

||| The located value is an actual node in the ordinary elaborated let spine.
data DefinitionAt : List Declaration -> C.Term n -> String -> C.Term m -> C.Term m -> Type where
  AtHead : {0 decl : Declaration} -> {0 rest : List Declaration} -> {0 q : Quantity} ->
    {0 signature, termValue : C.Term n} -> {0 termBody : C.Term (S n)} ->
    DefinitionAt (decl :: rest) (Apply (Lambda q signature termBody) termValue) decl.name signature termValue
  AtLater : {0 decl : Declaration} -> {0 q : Quantity} -> {0 domain, argument : C.Term n} ->
    {0 termBody : C.Term (S n)} -> {0 endpointName : String} -> {0 signature, termValue : C.Term m} ->
    DefinitionAt rest termBody endpointName signature termValue ->
    DefinitionAt (decl :: rest) (Apply (Lambda q domain termBody) argument) endpointName signature termValue

record LocatedDefinition (decls : List Declaration) (program : C.Term n) (name : String) where
  constructor LocatedDefinitionValue
  scope : Nat
  actualType : C.Term scope
  actualValue : C.Term scope
  site : DefinitionAt decls program name actualType actualValue

locateDefinition : {n : Nat} -> (decls : List Declaration) -> (program : C.Term n) -> (name : String) ->
  Maybe (LocatedDefinition decls program name)
locateDefinition [] program name = Nothing
locateDefinition (decl :: rest) (Apply (Lambda q ty body) value) name = case decEq name decl.name of
  Yes Refl => Just (LocatedDefinitionValue _ ty value AtHead)
  No _ => do
    LocatedDefinitionValue scope ty value site <- locateDefinition rest body name
    Just (LocatedDefinitionValue scope ty value (AtLater site))
locateDefinition _ _ _ = Nothing

noVariable : Fin 0 -> Fin n
noVariable v impossible

record CheckedEndpoint (decls : List Declaration) (program : C.Term 0) (name : String) where
  constructor Endpoint
  definition : CheckedPureDefinition
  located : LocatedDefinition decls program name
  exactContextualType : C.rename Application.noVariable definition.rawType = located.actualType
  exactContextualValue : C.rename Application.noVariable definition.rawValue = located.actualValue

checkEndpoint : (decls : List Declaration) -> (program : C.Term 0) -> (decl : Declaration) ->
  Either ElaborationError (CheckedEndpoint decls program decl.name)
checkEndpoint decls program decl = do
  definition <- checkDefinition decl
  case locateDefinition decls program decl.name of
    Nothing => failAt decl "endpoint is not an actual executable source declaration"
    Just located => case (samePureCore (C.rename Application.noVariable definition.rawType) located.actualType,
                          samePureCore (C.rename Application.noVariable definition.rawValue) located.actualValue) of
      (Just typeExact, Just valueExact) => Right (Endpoint definition located typeExact valueExact)
      _ => failAt decl "actual contextual definition differs from its independently checked closed image"

endpointAdmission : {0 endpointName : String} -> CheckedEndpoint decls program endpointName -> AdmissionTerm 0
endpointAdmission endpoint = pureAdmission endpoint.definition.image.pureTerm endpoint.definition.image.annotations

data CheckedProofEvidence : {0 decls : List Declaration} -> {0 program : C.Term 0} ->
  {0 leftName, rightName : String} ->
  (left : CheckedEndpoint decls program leftName) -> (right : CheckedEndpoint decls program rightName) -> Type where
  ConstantPathEvidence : {left : CheckedEndpoint decls program leftName} -> {right : CheckedEndpoint decls program rightName} ->
    left.definition.rawValue = right.definition.rawValue ->
    AdmittedCanonicalAbstractionInput [] ADNil {d = 0} STop
      (APOrdinary (endpointAdmission left)) (APOrdinary (endpointAdmission right))
      (APOrdinary (endpointAdmission left)) (shadowType left.definition.image.ty) ->
    CheckedProofEvidence left right
  BoolCasesEvidence : {left : CheckedEndpoint decls program leftName} -> {right : CheckedEndpoint decls program rightName} ->
    (lf : BoolFunction left.definition.image.pureTerm) ->
    (rf : BoolFunction right.definition.image.pureTerm) ->
    BoolAgreement (functionBody lf) (functionBody rf) -> CheckedProofEvidence left right

record CheckedCubicalProof (decls : List Declaration) (program : C.Term 0) where
  constructor CheckedProof
  name : String
  leftName : String
  rightName : String
  left : CheckedEndpoint decls program leftName
  right : CheckedEndpoint decls program rightName
  sameTypes : left.definition.image.ty = right.definition.image.ty
  evidence : CheckedProofEvidence left right

admissionError : AdmissionError -> String
admissionError InputLimit = "InputLimit"
admissionError CheckingLimit = "CheckingLimit"
admissionError TypeMismatch = "TypeMismatch"
admissionError SyntaxMismatch = "SyntaxMismatch"
admissionError UnsupportedEquality = "UnsupportedEquality"
admissionError SolverLimit = "SolverLimit"
admissionError FaceMismatch = "FaceMismatch"

checkGuard : (decls : List Declaration) -> (program : C.Term 0) -> List Declaration ->
  Declaration -> CubicalRule -> String -> String -> Either ElaborationError (CheckedCubicalProof decls program)
checkGuard decls program previous guard rule leftName rightName = do
  leftDecl <- case find (\decl => decl.name == leftName) previous of
    Nothing => failAt guard ("unknown or forward endpoint " ++ show leftName)
    Just decl => Right decl
  rightDecl <- case find (\decl => decl.name == rightName) previous of
    Nothing => failAt guard ("unknown or forward endpoint " ++ show rightName)
    Just decl => Right decl
  left <- checkEndpoint decls program leftDecl
  right <- checkEndpoint decls program rightDecl
  types <- case samePureType left.definition.image.ty right.definition.image.ty of
    Nothing => failAt guard "endpoint types/quantities differ"
    Just exact => Right exact
  evidence <- case rule of
    ConstantRefl => case samePureCore left.definition.rawValue right.definition.rawValue of
      Nothing => failAt guard "endpoints are not structurally identical (no beta/eta or algorithm-equivalence rule)"
      Just exact =>
        case admitCanonicalCommonAbstraction (MkCanonicalEqualityBudget (MkAdmissionBudget 4096 1024) 0)
               [] ADNil {d = 0} STop (APOrdinary (endpointAdmission left)) (APOrdinary (endpointAdmission right))
               (APOrdinary (endpointAdmission left)) (shadowType left.definition.image.ty) AERefl AERefl of
          Left err => failAt guard ("constant abstraction admission failed: " ++ admissionError err)
          Right evidence => Right (ConstantPathEvidence exact evidence)
    SemanticBoolCases => do
      (remaining, lf) <- case readBoolFunction 1024 left.definition.image.pureTerm of
        Nothing => failAt guard "boolCases left endpoint unsupported or body-node allowance exhausted (unary Bool lambda; variable/literal/if only)"
        Just checked => Right checked
      (_, rf) <- case readBoolFunction remaining right.definition.image.pureTerm of
        Nothing => failAt guard "boolCases right endpoint unsupported or shared body-node allowance exhausted (unary Bool lambda; variable/literal/if only)"
        Just checked => Right checked
      falseEqual <- case decEq (evaluateBody (functionBody lf) False) (evaluateBody (functionBody rf) False) of
        No _ => failAt guard "boolCases disagreement at False"
        Yes exact => Right exact
      trueEqual <- case decEq (evaluateBody (functionBody lf) True) (evaluateBody (functionBody rf) True) of
        No _ => failAt guard "boolCases disagreement at True"
        Yes exact => Right exact
      Right (BoolCasesEvidence lf rf (ByBoolCases falseEqual trueEqual))
  Right (CheckedProof guard.name leftDecl.name rightDecl.name left right types evidence)

consumes : ParsedDocument -> Declaration -> Declaration -> Bool
consumes document consumer endpoint = any referencesEndpoint (documentReferencesUsing id (const Nothing) document)
  where
    referencesEndpoint : Reference -> Bool
    referencesEndpoint reference =
      reference.target.start.offset == endpoint.definitionNameSpan.start.offset &&
      reference.target.finish.offset == endpoint.definitionNameSpan.finish.offset &&
      reference.origin.start.offset >= (extent consumer.value).start.offset &&
      reference.origin.finish.offset <= (extent consumer.value).finish.offset

proofUsedAsTerm : ParsedDocument -> Declaration -> Bool
proofUsedAsTerm document guard = any (\reference =>
  reference.target.start.offset == guard.definitionNameSpan.start.offset &&
  reference.target.finish.offset == guard.definitionNameSpan.finish.offset &&
  reference.origin.start.offset >= guard.span.finish.offset)
  (documentReferencesUsing id (const Nothing) document)

checkAll : (decls : List Declaration) -> (program : C.Term 0) -> ParsedDocument ->
  List Declaration -> List (CheckedCubicalProof decls program) -> List String -> List Declaration ->
  Either ElaborationError (List (CheckedCubicalProof decls program))
checkAll decls program document previous guards used [] =
  case find (\guard => not (elem guard.name used)) guards of
    Nothing => Right (reverse guards)
    Just guard => Left (ElaborationFailure document.end ("Cubical guard: unused proof " ++ show guard.name))
checkAll decls program document previous guards used (decl :: rest) = case decl.cubicalProof of
  Just (rule, left, right) => do
    if proofUsedAsTerm document decl
      then failAt decl "proof labels are not ordinary terms (including same-spelled Prelude names)" else Right ()
    guard <- checkGuard decls program previous decl rule left right
    checkAll decls program document previous (guard :: guards) used rest
  Nothing => do
    used <- case decl.requiredPath of
      Nothing => Right used
      Just name => case find (\guard => guard.name == name) guards of
        Nothing => failAt decl ("unknown or forward proof " ++ show name)
        Just guard => case find (\endpoint => endpoint.name == guard.leftName) previous of
          Nothing => failAt decl "proof endpoint is no longer in scope"
          Just endpoint => if consumes document decl endpoint then Right (name :: used)
            else failAt decl "requires consumer must reference the actual left endpoint in its body (not a shadowing binder)"
    checkAll decls program document (decl :: previous) guards used rest

proofReport : CheckedCubicalProof decls program -> String
proofReport guard = case guard.evidence of
  ConstantPathEvidence _ _ => "Cubical " ++ guard.name ++ ": checked constant-path guard (by refl)."
  BoolCasesEvidence _ _ _ => "Cubical " ++ guard.name ++ ": verified pointwise Bool agreement (by boolCases); not a cubical path."

||| Invoked after normal elaboration, before every standalone checking/execution
||| entry point. Evidence is erased metadata, never a core conversion or a cast.
public export
checkCubicalProofs : ParsedDocument -> List Declaration -> C.Term 0 -> Either ElaborationError (List String)
checkCubicalProofs document declarations program =
  map (map proofReport) (checkAll (executableDeclarations declarations) program document [] [] [] declarations)
