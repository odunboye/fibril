-- Experimental erased ordinary-fragment checker, not the Fibril kernel.
-- Theory: ATKEY18 sec. 2.1.3; details/departures in docs/erased-checker.md.
-- Primitive Unit/Bool rules are local designs; see docs/unit.md, docs/boolean.md.
module Fibril.Core.Erased

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Data.List
import Fibril.Core.GlobalTraversal
import Fibril.Termination.Extract
import Fibril.Core.Size
import Fibril.Core.Pretty
import Fibril.Core.Context
import Fibril.Core.Compatibility
import Fibril.Core.WeakHead
import Fibril.Core.Reduction
import Fibril.Core.FixAdmission

%default total

||| Failures distinguish exhausted checking/reduction from actual rejection.
public export
data CheckError : Type where
  GlobalError : String -> CheckError
  NatError : String -> CheckError
  RecursiveDataError : String -> CheckError
  NominalError : String -> CheckError
  RecursionError : String -> CheckError
  VariantError : String -> CheckError
  RegionError : String -> CheckError
  CheckingLimit : CheckError
  ReductionLimit : CheckError
  ExpectedUniverse : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedPairMotive : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedBoxMotive : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedBoxType : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedPairType : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedFunction : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedFileHandle : {0 n : Nat} -> (found : Term n) -> CheckError
  ||| Both types retain a shared scope; payloads are diagnostic data, not proofs.
  TypeMismatch : {0 n : Nat} -> (actual, expected : Term n) -> CheckError
  BranchTypeMismatch : {0 n : Nat} -> (yesType, noType : Term n) -> CheckError

public export
Show CheckError where
  show (GlobalError message) = "Global: " ++ message
  show (NatError message) = "Nat: " ++ message
  show (RecursiveDataError message) = "Recursive data: " ++ message
  show (NominalError message) = "Nominal: " ++ message
  show (RecursionError message) = "Recursion: " ++ message
  show (VariantError message) = "Variant: " ++ message
  show (RegionError message) = "Region: " ++ message
  show CheckingLimit = "Checking recursion budget exhausted"
  show ReductionLimit = "Reduction budget exhausted"
  show (ExpectedUniverse found) = "Expected a universe; found: " ++ renderTerm found
  show (ExpectedPairMotive found) = "Expected an erased pair motive returning a universe; found: " ++ renderTerm found
  show (ExpectedPairType found) = "Expected a dependent pair type; found: " ++ renderTerm found
  show (ExpectedBoxMotive found) = "Expected an erased box motive returning a universe; found: " ++ renderTerm found
  show (ExpectedBoxType found) = "Expected a unary box type; found: " ++ renderTerm found
  show (ExpectedFunction found) = "Expected a dependent function type; found: " ++ renderTerm found
  show (ExpectedFileHandle found) = "Expected a file handle type; found: " ++ renderTerm found
  show (TypeMismatch actual expected) =
    "Inferred type is not compatible with expected type; inferred: " ++ renderTerm actual ++
    "; expected: " ++ renderTerm expected
  show (BranchTypeMismatch yesType noType) =
    "Conditional branch types are not equal; then: " ++ renderTerm yesType ++
    "; else: " ++ renderTerm noType

||| Immutable, erased-checked declarations. The constructor is private:
||| arbitrary signatures cannot be supplied as typing certificates.
export
data GlobalContext : Type where
  CheckedGlobalContext : List (Nat, Quantity, Term 0, Term 0) -> GlobalContext

public export
emptyGlobals : GlobalContext
emptyGlobals = CheckedGlobalContext []

||| Read-only declaration inventory, newest first. These terms alone are not certificates.
public export
globalDeclarations : GlobalContext -> List (Nat, Quantity, Term 0, Term 0)
globalDeclarations (CheckedGlobalContext entries) = entries

||| Whole stored syntax, charging every signature and body once, including erased fields.
public export
globalSyntaxNodes : GlobalContext -> Nat
globalSyntaxNodes globals = foldr (\(_, _, ty, body), rest => coreNodes ty + coreNodes body + rest) 0 (globalDeclarations globals)

lookupEntry : Nat -> List (Nat, Quantity, Term 0, Term 0) -> Maybe (Quantity, Term 0, Term 0)
lookupEntry key [] = Nothing
lookupEntry key ((identity, q, ty, body) :: rest) =
  if key == identity then Just (q, ty, body) else lookupEntry key rest

public export
globalEntry : GlobalContext -> Nat -> Maybe (Quantity, Term 0, Term 0)
globalEntry (CheckedGlobalContext entries) key = lookupEntry key entries

public export
globalValue : GlobalContext -> Nat -> Maybe (Term 0)
globalValue globals key = do
  (_, _, body) <- globalEntry globals key
  Just body

-- References cannot hide syntax outside the existing termination fragment.
-- Every reachable closed signature/body is inspected once; no inlining is needed.
fixGlobalSyntax : GlobalContext -> Nat -> List Nat -> List Nat -> Either String ()
fixGlobalSyntax globals fuel [] seen = Right ()
fixGlobalSyntax globals Z (_ :: _) seen = Left "global termination syntax traversal exhausted"
fixGlobalSyntax globals (S fuel) (key :: rest) seen =
  if elem key seen then fixGlobalSyntax globals fuel rest seen else
    case globalEntry globals key of
      Nothing => Left ("unknown termination global " ++ show key)
      Just (_, ty, body) => do
        checkClosedGlobalSyntax ty
        checkClosedGlobalSyntax body
        fixGlobalSyntax globals fuel (globalReferences ty ++ globalReferences body ++ rest) (key :: seen)

-- Inspect only the outer type shape; comparison still uses full normalization.
exposeType : GlobalContext -> Nat -> Term n -> Either CheckError (Term n)
exposeType globals budget term =
  case weakHeadGlobals (globalValue globals) budget term of
    HeadForm result => Right result
    HeadLimit _ => Left ReductionLimit

||| A region result is copied to the parent arena, so it must be first-order data.
||| Shared with the runtime checker, which sees globals already expanded.
public export
checkRegionResultGlobals : GlobalContext -> Nat -> Term n -> Either CheckError ()
checkRegionResultGlobals globals budget resultType = do
  exposed <- exposeType globals budget resultType
  case exposed of
    Pi _ _ _ => Left (RegionError "result must be copyable data, not a function")
    IOType _ => Left (RegionError "result must be copyable data, not an IO description")
    FileHandleType _ => Left (RegionError "result must be copyable data, not a file handle")
    _ => Right ()

requireCompatible : GlobalContext -> Nat -> Term n -> Term n -> Either CheckError ()
requireCompatible globals budget actual expected =
  case compatibleTypesGlobals (globalValue globals) budget actual expected of
    Compatible => Right ()
    Incompatible => Left (TypeMismatch actual expected)
    CompatibilityLimit => Left ReductionLimit

-- Internal inference assumes context formation has already been checked.
-- Every recursive typing call decreases depth. Reduction has a separate budget.
mutual
  infer : GlobalContext -> Nat -> Nat -> Context n -> Term n -> Either CheckError (Term n)
  infer globals Z reduction context term = Left CheckingLimit
  infer globals (S depth) reduction context (GlobalRef key) =
    case globalEntry globals key of
      Nothing => Left (GlobalError ("unknown or forward reference " ++ show key))
      Just (_, ty, _) => Right (rename absurd ty)
  infer globals (S depth) reduction context (Variable i) = Right (lookupType i context)
  infer globals (S depth) reduction context (Universe level) = Right (Universe (S level))
  infer globals (S depth) reduction context UnitType = Right (Universe 0)
  infer globals (S depth) reduction context UnitValue = Right UnitType
  infer globals (S depth) reduction context BoolType = Right (Universe 0)
  infer globals (S depth) reduction context BoolTrue = Right BoolType
  infer globals (S depth) reduction context BoolFalse = Right BoolType
  infer globals (S depth) reduction context NatType = Right (Universe 0)
  infer globals (S depth) reduction context NatZero = Right NatType
  infer globals (S depth) reduction context (NatSucc value) = do
    ty <- infer globals depth reduction context value
    requireCompatible globals reduction ty NatType
    Right NatType
  infer globals (S depth) reduction context (NatCase motive value base more) = do
    valueType <- infer globals depth reduction context value
    requireCompatible globals reduction valueType NatType
    motiveType <- infer globals depth reduction context motive
    motiveHead <- exposeType globals reduction motiveType
    case motiveHead of
      Pi Erased parameter result => do
        requireCompatible globals reduction parameter NatType
        resultHead <- exposeType globals reduction result
        case resultHead of
          Universe _ => Right ()
          _ => Left (ExpectedUniverse resultHead)
      _ => Left (NatError "case motive must have an erased Nat binder and return a universe")
    baseType <- infer globals depth reduction context base
    requireCompatible globals reduction baseType (Apply motive NatZero)
    moreType <- infer globals depth reduction context more
    moreHead <- exposeType globals reduction moreType
    quantity <- case moreHead of
      Pi Linear _ _ => Right Linear
      Pi Unrestricted _ _ => Right Unrestricted
      _ => Left (NatError "case successor must have a linear or unrestricted Nat binder")
    let resultType = Apply (weaken motive) (NatSucc (Variable FZ))
    requireCompatible globals reduction moreType (Pi quantity NatType resultType)
    Right (Apply motive value)
  infer globals (S depth) reduction context (NatRec motive base next value) = do
    valueType <- infer globals depth reduction context value
    requireCompatible globals reduction valueType NatType
    motiveType <- infer globals depth reduction context motive
    motiveHead <- exposeType globals reduction motiveType
    case motiveHead of
      Pi Erased parameter result => do
        requireCompatible globals reduction parameter NatType
        resultHead <- exposeType globals reduction result
        case resultHead of
          Universe _ => Right ()
          _ => Left (ExpectedUniverse resultHead)
      _ => Left (NatError "recursor motive must have an erased Nat binder and return a universe")
    baseType <- infer globals depth reduction context base
    requireCompatible globals reduction baseType (Apply motive NatZero)
    nextType <- infer globals depth reduction context next
    let ihType = Apply (weaken motive) (Variable FZ)
    let resultType = Apply (weaken (weaken motive)) (NatSucc (Variable (FS FZ)))
    requireCompatible globals reduction nextType (Pi Erased NatType (Pi Linear ihType resultType))
    Right (Apply motive value)
  infer globals (S depth) reduction context (NatRecRuntime motive base next value) = do
    valueType <- infer globals depth reduction context value
    requireCompatible globals reduction valueType NatType
    motiveType <- infer globals depth reduction context motive
    motiveHead <- exposeType globals reduction motiveType
    case motiveHead of
      Pi Erased parameter result => do
        requireCompatible globals reduction parameter NatType
        resultHead <- exposeType globals reduction result
        case resultHead of
          Universe _ => Right ()
          _ => Left (ExpectedUniverse resultHead)
      _ => Left (NatError "recursor motive must have an erased Nat binder and return a universe")
    baseType <- infer globals depth reduction context base
    requireCompatible globals reduction baseType (Apply motive NatZero)
    nextType <- infer globals depth reduction context next
    let ihType = Apply (weaken motive) (Variable FZ)
    let resultType = Apply (weaken (weaken motive)) (NatSucc (Variable (FS FZ)))
    requireCompatible globals reduction nextType (Pi Unrestricted NatType (Pi Linear ihType resultType))
    Right (Apply motive value)
  infer globals (S depth) reduction context (RecType key) = Right (Universe 0)
  infer globals (S depth) reduction context (RecEnd annotation) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      RecType _ => Right annotation
      _ => Left (RecursiveDataError "terminal constructor requires a recursive-data type")
  infer globals (S depth) reduction context (RecMore annotation tail) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      RecType _ => do
        tailType <- infer globals depth reduction context tail
        requireCompatible globals reduction tailType annotation
        Right annotation
      _ => Left (RecursiveDataError "recursive constructor requires a recursive-data type")
  infer globals (S depth) reduction context (RecFold motive base next value) = do
    valueType <- infer globals depth reduction context value
    exposed <- exposeType globals reduction valueType
    case exposed of
      RecType _ => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter exposed
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (RecursiveDataError "fold motive must have an erased matching binder and return a universe")
        baseType <- infer globals depth reduction context base
        requireCompatible globals reduction baseType (Apply motive (RecEnd exposed))
        nextType <- infer globals depth reduction context next
        let ihType = Apply (weaken motive) (Variable FZ)
        let resultType = Apply (weaken (weaken motive))
                         (RecMore (weaken (weaken exposed)) (Variable (FS FZ)))
        requireCompatible globals reduction nextType (Pi Erased exposed (Pi Linear ihType resultType))
        Right (Apply motive value)
      _ => Left (RecursiveDataError "fold scrutinee must have a recursive-data type")
  infer globals (S depth) reduction context (RecCase motive value base more) = do
    valueType <- infer globals depth reduction context value
    exposed <- exposeType globals reduction valueType
    case exposed of
      RecType _ => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter exposed
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (RecursiveDataError "case motive must have an erased matching binder and return a universe")
        baseType <- infer globals depth reduction context base
        requireCompatible globals reduction baseType (Apply motive (RecEnd exposed))
        moreType <- infer globals depth reduction context more
        let resultType = Apply (weaken motive) (RecMore (weaken exposed) (Variable FZ))
        requireCompatible globals reduction moreType (Pi Linear exposed resultType)
        Right (Apply motive value)
      _ => Left (RecursiveDataError "case scrutinee must have a unary recursive-data type")
  infer globals (S depth) reduction context (SeqType key element) = do
    level <- sortOf globals depth reduction context element
    if level == 0 then Right (Universe 0)
      else Left (RecursiveDataError "sequence element must have universe level zero")
  infer globals (S depth) reduction context (SeqNil annotation) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      SeqType _ _ => Right annotation
      _ => Left (RecursiveDataError "empty constructor requires a sequence type")
  infer globals (S depth) reduction context (SeqCons annotation head tail) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      SeqType _ element => do
        headType <- infer globals depth reduction context head
        requireCompatible globals reduction headType element
        tailType <- infer globals depth reduction context tail
        requireCompatible globals reduction tailType annotation
        Right annotation
      _ => Left (RecursiveDataError "cons constructor requires a sequence type")
  infer globals (S depth) reduction context (SeqFold motive base next value) = do
    valueType <- infer globals depth reduction context value
    exposed <- exposeType globals reduction valueType
    case exposed of
      SeqType _ element => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter exposed
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (RecursiveDataError "fold motive must have an erased matching binder and return a universe")
        baseType <- infer globals depth reduction context base
        requireCompatible globals reduction baseType (Apply motive (SeqNil exposed))
        nextType <- infer globals depth reduction context next
        let ihType = Apply (weaken (weaken motive)) (Variable FZ)
        let cons = SeqCons (weaken (weaken (weaken exposed))) (Variable (FS (FS FZ))) (Variable (FS FZ))
        let resultType = Apply (weaken (weaken (weaken motive))) cons
        requireCompatible globals reduction nextType (Pi Linear element (Pi Erased (weaken exposed) (Pi Linear ihType resultType)))
        Right (Apply motive value)
      _ => Left (RecursiveDataError "fold scrutinee must have a sequence type")
  infer globals (S depth) reduction context (SeqCase motive value base cons) = do
    valueType <- infer globals depth reduction context value
    exposed <- exposeType globals reduction valueType
    case exposed of
      SeqType _ element => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter exposed
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (RecursiveDataError "sequence case motive must have an erased matching binder and return a universe")
        baseType <- infer globals depth reduction context base
        requireCompatible globals reduction baseType (Apply motive (SeqNil exposed))
        consType <- infer globals depth reduction context cons
        let constructed = SeqCons (weaken (weaken exposed)) (Variable (FS FZ)) (Variable FZ)
        let resultType = Apply (weaken (weaken motive)) constructed
        requireCompatible globals reduction consType (Pi Linear element (Pi Linear (weaken exposed) resultType))
        Right (Apply motive value)
      _ => Left (RecursiveDataError "case scrutinee must have a sequence type")
  infer globals (S depth) reduction context ReadLine = Right (IOType readResultType)
  infer globals (S depth) reduction context (FileHandleValue identity _) = Right (FileHandleType (runtimeFileRegion identity))
  infer globals (S depth) reduction context (ReadInputFile handle) = do
    handleType <- infer globals depth reduction context handle
    exposed <- exposeType globals reduction handleType
    case exposed of
      FileHandleType region => Right (IOType (fileReadResultType region))
      _ => Left (ExpectedFileHandle exposed)
  infer globals (S depth) reduction context (BytesLengthIs count bytes) = do
    countType <- infer globals depth reduction context count
    requireCompatible globals reduction countType NatType
    bytesType <- infer globals depth reduction context bytes
    requireCompatible globals reduction bytesType BytesType
    Right BoolType
  infer globals (S depth) reduction context (BytesIndex index bytes) = do
    indexType <- infer globals depth reduction context index
    requireCompatible globals reduction indexType NatType
    bytesType <- infer globals depth reduction context bytes
    requireCompatible globals reduction bytesType BytesType
    Right byteIndexResultType
  infer globals (S depth) reduction context (BytesSlice start count bytes) = do
    startType <- infer globals depth reduction context start
    requireCompatible globals reduction startType NatType
    countType <- infer globals depth reduction context count
    requireCompatible globals reduction countType NatType
    bytesType <- infer globals depth reduction context bytes
    requireCompatible globals reduction bytesType BytesType
    Right BytesType
  infer globals (S depth) reduction context (UTF8Encode x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty StringType
    Right (utf8ResultType BytesType)
  infer globals (S depth) reduction context (UTF8Decode x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty BytesType
    Right (utf8ResultType StringType)
  infer globals (S depth) reduction context BytesType = Right (Universe 0)
  infer globals (S depth) reduction context (BytesValue _) = Right BytesType
  infer globals (S depth) reduction context (WithRegion resultType body) = do
    resultSort <- infer globals depth reduction context resultType
    requireCompatible globals reduction resultSort (Universe 0)
    -- The result cannot mention the bound region, so it cannot escape it.
    checkRegionResultGlobals globals reduction resultType
    bodyType <- infer globals depth reduction context body
    requireCompatible globals reduction bodyType (Pi Erased (Universe 0) (weaken resultType))
    Right resultType
  infer globals (S depth) reduction context (BytesAppend a b) = do
    aType <- infer globals depth reduction context a
    requireCompatible globals reduction aType BytesType
    bType <- infer globals depth reduction context b
    requireCompatible globals reduction bType BytesType
    Right BytesType
  infer globals (S depth) reduction context (BytesShare x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty BytesType
    Right (BoxType Unrestricted BytesType)
  infer globals (S depth) reduction context (BytesLength x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty BytesType
    Right NatType
  infer globals (S depth) reduction context (BytesOctet x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty NatType
    Right BytesType
  infer globals (S depth) reduction context (IterateBinary stateType resultType count step initial) = do
    stateSort <- infer globals depth reduction context stateType
    requireCompatible globals reduction stateSort (Universe 0)
    resultSort <- infer globals depth reduction context resultType
    requireCompatible globals reduction resultSort (Universe 0)
    countType <- infer globals depth reduction context count
    requireCompatible globals reduction countType NatType
    stepType <- infer globals depth reduction context step
    requireCompatible globals reduction stepType (binaryStepType stateType resultType)
    initialType <- infer globals depth reduction context initial
    requireCompatible globals reduction initialType stateType
    Right (IOType (loopVariantType stateType resultType))
  infer globals (S depth) reduction context (ReadBytes x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty NatType
    Right (IOType byteReadResultType)
  infer globals (S depth) reduction context (WriteBytes x) = do
    ty <- infer globals depth reduction context x
    requireCompatible globals reduction ty BytesType
    Right (IOType UnitType)
  infer globals (S depth) reduction context RejectBytes = Right (IOType UnitType)
  infer globals (S depth) reduction context FlushBytes = Right (IOType UnitType)
  infer globals (S depth) reduction context StringType = Right (Universe 0)
  infer globals (S depth) reduction context (StringValue _) = Right StringType
  infer globals (S depth) reduction context (StringAppend left right) = do
    leftType <- infer globals depth reduction context left
    requireCompatible globals reduction leftType StringType
    rightType <- infer globals depth reduction context right
    requireCompatible globals reduction rightType StringType
    Right StringType
  infer globals (S depth) reduction context (StringEqual left right) = do
    leftType <- infer globals depth reduction context left
    requireCompatible globals reduction leftType StringType
    rightType <- infer globals depth reduction context right
    requireCompatible globals reduction rightType StringType
    Right BoolType
  infer globals (S depth) reduction context (FileHandleType region) = do
    regionType <- infer globals depth reduction context region
    requireCompatible globals reduction regionType (Universe 0)
    Right (Universe 0)
  infer globals (S depth) reduction context (WithInputFile result path body) = do
    resultSort <- infer globals depth reduction context result
    requireCompatible globals reduction resultSort (Universe 0)
    pathType <- infer globals depth reduction context path
    requireCompatible globals reduction pathType StringType
    bodyType <- infer globals depth reduction context body
    requireCompatible globals reduction bodyType (scopedInputBodyType result)
    Right (IOType (fileScopeResultType result))
  infer globals (S depth) reduction context (IOType ty) = do
    level <- sortOf globals depth reduction context ty
    Right (Universe level)
  infer globals (S depth) reduction context (IOPure value) = do
    ty <- infer globals depth reduction context value
    Right (IOType ty)
  infer globals (S depth) reduction context (WriteLine text) = do
    ty <- infer globals depth reduction context text
    requireCompatible globals reduction ty StringType
    Right (IOType UnitType)
  infer globals (S depth) reduction context (IOBind a b action next) = do
    _ <- sortOf globals depth reduction context a
    _ <- sortOf globals depth reduction context b
    actionType <- infer globals depth reduction context action
    requireCompatible globals reduction actionType (IOType a)
    nextType <- infer globals depth reduction context next
    requireCompatible globals reduction nextType (Pi Linear a (weaken (IOType b)))
    Right (IOType b)
  infer globals (S depth) reduction context (BoolCase condition yes no) = do
    conditionType <- infer globals depth reduction context condition
    requireCompatible globals reduction conditionType BoolType
    yesType <- infer globals depth reduction context yes
    noType <- infer globals depth reduction context no
    case betaCompareGlobals (globalValue globals) reduction yesType noType of
      EqualNormalForms => Right yesType
      DifferentNormalForms => Left (BranchTypeMismatch yesType noType)
      Inconclusive => Left ReductionLimit
  infer globals (S depth) reduction context (NominalType key indices shape) = do
    nominalIndices globals depth reduction context indices
    level <- sortOf globals depth reduction context shape
    exposed <- exposeType globals reduction shape
    case exposed of
      VariantType _ => Right (Universe level)
      _ => Left (NominalError "nominal shape must expose a variant type")
  infer globals (S depth) reduction context (NominalValue annotation value) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      NominalType _ _ shape => do
        actual <- infer globals depth reduction context value
        requireCompatible globals reduction actual shape
        Right annotation
      _ => Left (NominalError "nominal value annotation must expose a nominal type")
  infer globals (S depth) reduction context (NominalCase motive scrutinee branch) = do
    ty <- infer globals depth reduction context scrutinee
    exposed <- exposeType globals reduction ty
    case exposed of
      NominalType _ _ shape => do
        motiveType <- infer globals depth reduction context motive
        exposedMotive <- exposeType globals reduction motiveType
        case exposedMotive of
          Pi Erased domain result => do
            requireCompatible globals reduction domain exposed
            resultSort <- exposeType globals reduction result
            case resultSort of
              Universe _ => Right ()
              _ => Left (NominalError "nominal motive must return a universe")
          _ => Left (NominalError "nominal motive must have an erased matching domain")
        actual <- infer globals depth reduction context branch
        requireCompatible globals reduction actual
          (Pi Linear shape (Apply (weaken motive) (NominalValue (weaken exposed) (Variable FZ))))
        Right (Apply motive scrutinee)
      _ => Left (NominalError "nominal case scrutinee must have a nominal type")
  infer globals (S depth) reduction context (VariantType []) = Left (VariantError "empty alternatives are not admitted")
  infer globals (S depth) reduction context (VariantType arms) = Universe <$> variantSort globals depth reduction context arms
  infer globals (S depth) reduction context (VariantValue annotation tag payload) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      VariantType arms => case (variantAt tag arms, payload) of
        (Just Nothing, Nothing) => Right annotation
        (Just (Just (_, domain)), Just value) => do
          actual <- infer globals depth reduction context value
          requireCompatible globals reduction actual domain
          Right annotation
        _ => Left (VariantError "constructor tag or payload arity is invalid")
      _ => Left (VariantError "constructor annotation must expose a variant type")
  -- Phase 1 of docs/general-recursive-data-plan.md: the terms exist, typing does not. Refusing
  -- keeps them from being admitted by accident until their rules are written and tested.
  infer globals (S depth) reduction context (DataType _) = Left (RecursiveDataError "general recursive data typing is not implemented")
  infer globals (S depth) reduction context (DataCon _ _ _) = Left (RecursiveDataError "general recursive data typing is not implemented")
  infer globals (S depth) reduction context (DataCase _ _ _ _) = Left (RecursiveDataError "general recursive data typing is not implemented")
  infer globals (S depth) reduction context (VariantCase motive scrutinee branches) = do
    ty <- infer globals depth reduction context scrutinee
    exposed <- exposeType globals reduction ty
    case exposed of
      VariantType arms => do
        motiveType <- infer globals depth reduction context motive
        exposedMotive <- exposeType globals reduction motiveType
        case exposedMotive of
          Pi Erased domain result => do
            requireCompatible globals reduction domain exposed
            resultSort <- exposeType globals reduction result
            case resultSort of
              Universe _ => Right ()
              _ => Left (VariantError "motive must return a universe")
          _ => Left (VariantError "motive must have an erased matching domain")
        variantBranches globals depth reduction context motive exposed 0 arms branches
        Right (Apply motive scrutinee)
      _ => Left (VariantError "case scrutinee must have a variant type")
  infer globals (S depth) reduction context (BoxType q domain) = do
    level <- sortOf globals depth reduction context domain
    Right (Universe level)
  infer globals (S depth) reduction context (BoxValue annotation value) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      BoxType q domain => do
        valueType <- infer globals depth reduction context value
        requireCompatible globals reduction valueType domain
        Right annotation
      _ => Left (ExpectedBoxType exposed)
  infer globals (S depth) reduction context (BoxCase motive scrutinee branch) = do
    scrutineeType <- infer globals depth reduction context scrutinee
    exposed <- exposeType globals reduction scrutineeType
    case exposed of
      BoxType q domain => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter scrutineeType
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (ExpectedBoxMotive motiveHead)
        let packed = BoxValue (weaken scrutineeType) (Variable FZ)
        let resultType = Apply (weaken motive) packed
        branchType <- infer globals depth reduction context branch
        requireCompatible globals reduction branchType (Pi q domain resultType)
        Right (Apply motive scrutinee)
      _ => Left (ExpectedBoxType exposed)
  infer globals (S depth) reduction context (Sigma q r domain body) = do
    domainLevel <- sortOf globals depth reduction context domain
    bodyLevel <- sortOf globals depth reduction (Extend context q domain) body
    Right (Universe (max domainLevel bodyLevel))
  infer globals (S depth) reduction context (PairCase motive scrutinee branch) = do
    scrutineeType <- infer globals depth reduction context scrutinee
    exposed <- exposeType globals reduction scrutineeType
    case exposed of
      Sigma q r domain body => do
        motiveType <- infer globals depth reduction context motive
        motiveHead <- exposeType globals reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible globals reduction parameter scrutineeType
            resultHead <- exposeType globals reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (ExpectedPairMotive motiveHead)
        let packed = PairValue (weaken (weaken scrutineeType))
                               (Variable (FS FZ)) (Variable FZ)
        let resultType = Apply (weaken (weaken motive)) packed
        branchType <- infer globals depth reduction context branch
        requireCompatible globals reduction branchType (Pi q domain (Pi r body resultType))
        Right (Apply motive scrutinee)
      _ => Left (ExpectedPairType exposed)
  infer globals (S depth) reduction context (PairValue annotation first second) = do
    _ <- sortOf globals depth reduction context annotation
    exposed <- exposeType globals reduction annotation
    case exposed of
      Sigma q r domain body => do
        firstType <- infer globals depth reduction context first
        requireCompatible globals reduction firstType domain
        secondType <- infer globals depth reduction context second
        requireCompatible globals reduction secondType (instantiateTerm first body)
        Right annotation
      _ => Left (ExpectedPairType exposed)
  infer globals (S depth) reduction context (Pi q domain body) = do
    domainLevel <- sortOf globals depth reduction context domain
    bodyLevel <- sortOf globals depth reduction (Extend context q domain) body
    Right (Universe (max domainLevel bodyLevel))
  infer globals (S depth) reduction context (Lambda q domain body) = do
    _ <- sortOf globals depth reduction context domain
    bodyType <- infer globals depth reduction (Extend context q domain) body
    Right (Pi q domain bodyType)
  -- Fix: the self reference is unrestricted and typed by the declared function
  -- type; the body is checked against that type, then a separate admission gate runs.
  infer globals (S depth) reduction context (Fix ty body) = do
    _ <- sortOf globals depth reduction context ty
    exposed <- exposeType globals reduction ty
    case exposed of
      Pi _ _ _ => Right ()
      _ => Left (ExpectedFunction exposed)
    bodyType <- infer globals depth reduction (Extend context Unrestricted ty) body
    requireCompatible globals reduction bodyType (weaken ty)
    let dependencies = globalReferences ty ++ globalReferences body
    case fixGlobalSyntax globals (S (coreNodes ty + coreNodes body + globalSyntaxNodes globals)) dependencies [] of
      Left message => Left (RecursionError message)
      Right () => Right ()
    case admitFix ty body of
      Left message => Left (RecursionError message)
      Right () => Right ty
  infer globals (S depth) reduction context (Apply function argument) = do
    functionType <- infer globals depth reduction context function
    exposed <- exposeType globals reduction functionType
    case exposed of
      Pi q domain body => do
        argumentType <- infer globals depth reduction context argument
        requireCompatible globals reduction argumentType domain
        Right (instantiateTerm argument body)
      _ => Left (ExpectedFunction exposed)

  infer globals (S depth) reduction context (UnitCase scrutinee body) = do
    scrutineeType <- infer globals depth reduction context scrutinee
    requireCompatible globals reduction scrutineeType UnitType
    infer globals depth reduction context body

  nominalIndices : GlobalContext -> Nat -> Nat -> Context n -> List (Term n) -> Either CheckError ()
  nominalIndices globals _ _ _ [] = Right ()
  nominalIndices globals Z _ _ (_ :: _) = Left CheckingLimit
  nominalIndices globals (S depth) reduction context (index :: rest) = do
    _ <- infer globals depth reduction context index
    nominalIndices globals depth reduction context rest

  variantSort : GlobalContext -> Nat -> Nat -> Context n -> List (Maybe (Quantity, Term n)) -> Either CheckError Nat
  variantSort globals depth reduction context [] = Right 0
  variantSort globals Z reduction context (_ :: _) = Left CheckingLimit
  variantSort globals (S depth) reduction context (Nothing :: rest) = variantSort globals depth reduction context rest
  variantSort globals (S depth) reduction context (Just (_, ty) :: rest) = do
    level <- sortOf globals depth reduction context ty
    remaining <- variantSort globals depth reduction context rest
    Right (max level remaining)

  variantBranches : GlobalContext -> Nat -> Nat -> Context n -> Term n -> Term n -> Nat ->
                    List (Maybe (Quantity, Term n)) -> List (Term n) -> Either CheckError ()
  variantBranches globals depth reduction context motive ty tag [] [] = Right ()
  variantBranches globals Z reduction context motive ty tag (_ :: _) (_ :: _) = Left CheckingLimit
  variantBranches globals (S depth) reduction context motive ty tag (arm :: arms) (branch :: branches) = do
    actual <- infer globals depth reduction context branch
    requireCompatible globals reduction actual (variantBranchType motive ty tag arm)
    variantBranches globals depth reduction context motive ty (S tag) arms branches
  variantBranches globals _ _ _ _ _ _ _ _ = Left (VariantError "case requires exactly one branch per alternative")

  sortOf : GlobalContext -> Nat -> Nat -> Context n -> Term n -> Either CheckError Nat
  sortOf globals depth reduction context term = do
    ty <- infer globals depth reduction context term
    exposed <- exposeType globals reduction ty
    case exposed of
      Universe level => Right level
      _ => Left (ExpectedUniverse exposed)

formation : GlobalContext -> Nat -> Nat -> Context n -> Either CheckError ()
formation globals depth reduction Empty = Right ()
formation globals Z reduction (Extend rest q domain) = Left CheckingLimit
formation globals (S depth) reduction (Extend rest q domain) = do
  formation globals depth reduction rest
  _ <- sortOf globals depth reduction rest domain
  Right ()

||| Check that each stored context domain is a type in its preceding context.
||| This erased judgment imposes no runtime coefficient obligations.
public export
checkErasedContextGlobals : GlobalContext -> (depth : Nat) -> (reduction : Nat) -> Context n -> Either CheckError ()
checkErasedContextGlobals globals = formation globals

||| Infer an ordinary term's type after validating its context.
||| This is erased-only: success does not authorize runtime resource use.
public export
inferErasedGlobals : GlobalContext -> (depth : Nat) -> (reduction : Nat) -> Context n -> Term n ->
              Either CheckError (Term n)
inferErasedGlobals globals depth reduction context term = do
  formation globals depth reduction context
  infer globals depth reduction context term

||| Validate expected type formation, infer the term, then check compatibility.
||| Literal universes lift upwards; Pi/quantity structure remains invariant.
public export
checkErasedGlobals : GlobalContext -> (depth : Nat) -> (reduction : Nat) -> Context n ->
              (term : Term n) -> (expected : Term n) -> Either CheckError ()
checkErasedGlobals globals depth reduction context term expected = do
  formation globals depth reduction context
  _ <- sortOf globals depth reduction context expected
  actual <- infer globals depth reduction context term
  requireCompatible globals reduction actual expected

||| Admit one closed declaration against the preceding environment only.
||| No self/forward references, duplicate identities or linear globals.
||| Runtime usage of non-erased bodies is checked separately by RuntimeGlobals.
public export
extendErasedGlobals : Nat -> Nat -> GlobalContext -> Nat -> Quantity -> Term 0 -> Term 0 ->
                     Either CheckError GlobalContext
extendErasedGlobals depth reduction globals@(CheckedGlobalContext entries) key q ty body = do
  case globalEntry globals key of
    Just _ => Left (GlobalError ("duplicate identity " ++ show key))
    Nothing => Right ()
  case q of
    Linear => Left (GlobalError "linear global ownership is unsupported")
    _ => Right ()
  checkErasedGlobals globals depth reduction Empty body ty
  Right (CheckedGlobalContext ((key, q, ty, body) :: entries))

public export
checkRegionResult : Nat -> Term n -> Either CheckError ()
checkRegionResult = checkRegionResultGlobals emptyGlobals

public export
checkErasedContext : Nat -> Nat -> Context n -> Either CheckError ()
checkErasedContext = checkErasedContextGlobals emptyGlobals

public export
inferErased : Nat -> Nat -> Context n -> Term n -> Either CheckError (Term n)
inferErased = inferErasedGlobals emptyGlobals

public export
checkErased : Nat -> Nat -> Context n -> Term n -> Term n -> Either CheckError ()
checkErased = checkErasedGlobals emptyGlobals
