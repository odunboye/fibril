||| Fail-closed admission to Common Path v0, not a production conversion API.
module Fibril.Cubical.Logical.CommonAdmission

import Data.Fin
import Data.Vect
import Decidable.Equality
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Scoped but untyped. Applications retain a domain annotation because the
||| common unannotated grammar does not determine application domains.
public export
data AdmissionTerm : Nat -> Type where
  AVar : Fin n -> AdmissionTerm n
  AUnit : AdmissionTerm n
  ABool : Bool -> AdmissionTerm n
  ALam : AdmissionTerm (S n) -> AdmissionTerm n
  AApp : LogicalType -> AdmissionTerm n -> AdmissionTerm n -> AdmissionTerm n
  AUnitElim : AdmissionTerm n -> AdmissionTerm n -> AdmissionTerm n
  AIf : AdmissionTerm n -> AdmissionTerm n -> AdmissionTerm n -> AdmissionTerm n

public export
eraseAdmission : AdmissionTerm n -> CommonTerm n
eraseAdmission (AVar i) = CVar i
eraseAdmission AUnit = CUnit
eraseAdmission (ABool b) = CBool b
eraseAdmission (ALam b) = CLam (eraseAdmission b)
eraseAdmission (AApp _ f x) = CApp (eraseAdmission f) (eraseAdmission x)
eraseAdmission (AUnitElim x b) = CUnitElim (eraseAdmission x) (eraseAdmission b)
eraseAdmission (AIf c t f) = CIf (eraseAdmission c) (eraseAdmission t) (eraseAdmission f)

public export
data AdmissionPathTerm : Nat -> Nat -> Nat -> Type where
  APOrdinary : AdmissionTerm n -> AdmissionPathTerm n k d
  APAt : Fin k -> ScopedInterval d -> AdmissionPathTerm n k d
  APLam : AdmissionPathTerm (S n) k d -> AdmissionPathTerm n k d
  APApp : LogicalType -> AdmissionPathTerm n k d -> AdmissionPathTerm n k d -> AdmissionPathTerm n k d
  APUnitElim : AdmissionPathTerm n k d -> AdmissionPathTerm n k d -> AdmissionPathTerm n k d
  APIf : AdmissionPathTerm n k d -> AdmissionPathTerm n k d -> AdmissionPathTerm n k d -> AdmissionPathTerm n k d

public export
eraseAdmissionPath : AdmissionPathTerm n k d -> CommonPathTerm n k d
eraseAdmissionPath (APOrdinary t) = CPOrdinary (eraseAdmission t)
eraseAdmissionPath (APAt p i) = CPAt p i
eraseAdmissionPath (APLam b) = CPLam (eraseAdmissionPath b)
eraseAdmissionPath (APApp _ f x) = CPApp (eraseAdmissionPath f) (eraseAdmissionPath x)
eraseAdmissionPath (APUnitElim x b) = CPUnitElim (eraseAdmissionPath x) (eraseAdmissionPath b)
eraseAdmissionPath (APIf c t f) = CPIf (eraseAdmissionPath c) (eraseAdmissionPath t) (eraseAdmissionPath f)

public export
data AdmissionError = InputLimit | CheckingLimit | TypeMismatch

||| Preflight counts all context/type/scope/index/interval/syntax constructors
||| together, before lookup, type comparison or proof construction. Checking
||| fuel counts rule nodes sequentially, not independently in each branch.
public export
record AdmissionBudget where
  constructor MkAdmissionBudget
  inputNodes : Nat
  checkingNodes : Nat

public export
record AdmittedTerm (ctx : Vect n LogicalType) (raw : AdmissionTerm n) (a : LogicalType) where
  constructor MkAdmittedTerm
  termTyping : CommonHasType ctx (eraseAdmission raw) a
  termWitness : HigherOrderTerm ctx a termTyping

public export
record AdmittedPathTerm (ctx : Vect n LogicalType) (paths : Vect k LogicalType)
  (d : Nat) (raw : AdmissionPathTerm n k d) (a : LogicalType) where
  constructor MkAdmittedPathTerm
  pathTyping : CommonPathHasType ctx paths (eraseAdmissionPath raw) a
  pathWitness : HigherOrderPathTerm ctx paths a d pathTyping

arrowDomain : LArrow a b = LArrow c d -> a = c
arrowDomain Refl = Refl

arrowResult : LArrow a b = LArrow c d -> b = d
arrowResult Refl = Refl

||| Constructive total equality; rejection is backed by a refutation too.
public export
commonTypeDecEq : (a, b : LogicalType) -> Dec (a = b)
commonTypeDecEq LUnit LUnit = Yes Refl
commonTypeDecEq LBool LBool = Yes Refl
commonTypeDecEq LUnit LBool = No (\Refl impossible)
commonTypeDecEq LBool LUnit = No (\Refl impossible)
commonTypeDecEq LUnit (LArrow a b) = No (\Refl impossible)
commonTypeDecEq LBool (LArrow a b) = No (\Refl impossible)
commonTypeDecEq (LArrow a b) LUnit = No (\Refl impossible)
commonTypeDecEq (LArrow a b) LBool = No (\Refl impossible)
commonTypeDecEq (LArrow a b) (LArrow c d) = case commonTypeDecEq a c of
  No contra => No (contra . arrowDomain)
  Yes Refl => case commonTypeDecEq b d of
    No contra => No (contra . arrowResult)
    Yes Refl => Yes Refl

spend : Nat -> Either AdmissionError Nat
spend Z = Left InputLimit
spend (S fuel) = Right fuel

preflightType : Nat -> LogicalType -> Either AdmissionError Nat
preflightType fuel LUnit = spend fuel
preflightType fuel LBool = spend fuel
preflightType fuel (LArrow a b) = do
  rest <- spend fuel
  rest <- preflightType rest a
  preflightType rest b

preflightContext : Nat -> Vect n LogicalType -> Either AdmissionError Nat
preflightContext fuel [] = spend fuel
preflightContext fuel (a :: ctx) = do
  rest <- spend fuel
  rest <- preflightType rest a
  preflightContext rest ctx

preflightScope : Nat -> Nat -> Either AdmissionError Nat
preflightScope fuel Z = spend fuel
preflightScope fuel (S n) = do
  rest <- spend fuel
  preflightScope rest n

preflightIndex : Nat -> Fin n -> Either AdmissionError Nat
preflightIndex fuel FZ = spend fuel
preflightIndex fuel (FS i) = do
  rest <- spend fuel
  preflightIndex rest i

preflightInterval : Nat -> ScopedInterval d -> Either AdmissionError Nat
preflightInterval fuel Zero = spend fuel
preflightInterval fuel One = spend fuel
preflightInterval fuel (Var i) = do
  rest <- spend fuel
  preflightIndex rest i
preflightInterval fuel (Reverse i) = do
  rest <- spend fuel
  preflightInterval rest i
preflightInterval fuel (Meet i j) = do
  rest <- spend fuel
  rest <- preflightInterval rest i
  preflightInterval rest j
preflightInterval fuel (Join i j) = do
  rest <- spend fuel
  rest <- preflightInterval rest i
  preflightInterval rest j

preflightTerm : Nat -> AdmissionTerm n -> Either AdmissionError Nat
preflightTerm fuel (AVar i) = do
  rest <- spend fuel
  preflightIndex rest i
preflightTerm fuel AUnit = spend fuel
preflightTerm fuel (ABool _) = spend fuel
preflightTerm fuel (ALam b) = do
  rest <- spend fuel
  preflightTerm rest b
preflightTerm fuel (AApp a f x) = do
  rest <- spend fuel
  rest <- preflightType rest a
  rest <- preflightTerm rest f
  preflightTerm rest x
preflightTerm fuel (AUnitElim x b) = do
  rest <- spend fuel
  rest <- preflightTerm rest x
  preflightTerm rest b
preflightTerm fuel (AIf c t f) = do
  rest <- spend fuel
  rest <- preflightTerm rest c
  rest <- preflightTerm rest t
  preflightTerm rest f

preflightPath : Nat -> AdmissionPathTerm n k d -> Either AdmissionError Nat
preflightPath fuel (APOrdinary t) = do
  rest <- spend fuel
  preflightTerm rest t
preflightPath fuel (APAt p i) = do
  rest <- spend fuel
  rest <- preflightIndex rest p
  preflightInterval rest i
preflightPath fuel (APLam b) = do
  rest <- spend fuel
  preflightPath rest b
preflightPath fuel (APApp a f x) = do
  rest <- spend fuel
  rest <- preflightType rest a
  rest <- preflightPath rest f
  preflightPath rest x
preflightPath fuel (APUnitElim x b) = do
  rest <- spend fuel
  rest <- preflightPath rest x
  preflightPath rest b
preflightPath fuel (APIf c t f) = do
  rest <- spend fuel
  rest <- preflightPath rest c
  rest <- preflightPath rest t
  preflightPath rest f

checkTerm : Nat -> (ctx : Vect n LogicalType) -> (raw : AdmissionTerm n) -> (a : LogicalType) ->
  Either AdmissionError (Nat, AdmittedTerm ctx raw a)
checkTerm Z ctx raw a = Left CheckingLimit
checkTerm (S fuel) ctx (AVar i) a = case commonTypeDecEq (index i ctx) a of
  No _ => Left TypeMismatch
  Yes Refl => Right (fuel,
    replace {p = \j => AdmittedTerm ctx (AVar j) (index i ctx)} (commonVarAtIndex ctx i)
      (MkAdmittedTerm (CVariable (commonVarAt ctx i)) (HOVar ctx (index i ctx) (commonVarAt ctx i))))
checkTerm (S fuel) ctx AUnit a = case commonTypeDecEq LUnit a of
  No _ => Left TypeMismatch
  Yes Refl => Right (fuel, MkAdmittedTerm CUnitType (HOUnit ctx))
checkTerm (S fuel) ctx (ABool b) a = case commonTypeDecEq LBool a of
  No _ => Left TypeMismatch
  Yes Refl => Right (fuel, MkAdmittedTerm CBoolType (HOBool ctx b))
checkTerm (S fuel) ctx (ALam body) (LArrow a b) = do
  (rest, MkAdmittedTerm ty w) <- checkTerm fuel (a :: ctx) body b
  Right (rest, MkAdmittedTerm (CLambdaType ty) (HOLambda ctx a b w))
checkTerm (S fuel) ctx (ALam body) LUnit = Left TypeMismatch
checkTerm (S fuel) ctx (ALam body) LBool = Left TypeMismatch
checkTerm (S fuel) ctx (AApp a f x) b = do
  (rest, MkAdmittedTerm ft fw) <- checkTerm fuel ctx f (LArrow a b)
  (rest, MkAdmittedTerm xt xw) <- checkTerm rest ctx x a
  Right (rest, MkAdmittedTerm (CApplicationType ft xt) (HOApplication ctx a b fw xw))
checkTerm (S fuel) ctx (AUnitElim x body) a = do
  (rest, MkAdmittedTerm xt xw) <- checkTerm fuel ctx x LUnit
  (rest, MkAdmittedTerm bt bw) <- checkTerm rest ctx body a
  Right (rest, MkAdmittedTerm (CUnitEliminationType xt bt) (HOUnitElim ctx a xw bw))
checkTerm (S fuel) ctx (AIf c t f) a = do
  (rest, MkAdmittedTerm ct cw) <- checkTerm fuel ctx c LBool
  (rest, MkAdmittedTerm tt tw) <- checkTerm rest ctx t a
  (rest, MkAdmittedTerm ft fw) <- checkTerm rest ctx f a
  Right (rest, MkAdmittedTerm (CConditionalType ct tt ft) (HOIf ctx a cw tw fw))

checkPath : Nat -> (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (d : Nat) ->
  (raw : AdmissionPathTerm n k d) -> (a : LogicalType) ->
  Either AdmissionError (Nat, AdmittedPathTerm ctx paths d raw a)
checkPath Z ctx paths d raw a = Left CheckingLimit
checkPath (S fuel) ctx paths d (APOrdinary t) a = do
  (rest, MkAdmittedTerm ty w) <- checkTerm fuel ctx t a
  Right (rest, MkAdmittedPathTerm (CPOrdinaryType ty) (HOPOrdinary ctx paths a d w))
checkPath (S fuel) ctx paths d (APAt p i) a = case commonTypeDecEq (index p paths) a of
  No _ => Left TypeMismatch
  Yes Refl => Right (fuel,
    replace {p = \j => AdmittedPathTerm ctx paths d (APAt j i) (index p paths)} (commonVarAtIndex paths p)
      (MkAdmittedPathTerm (CPAtType (commonVarAt paths p))
        (HOPAt ctx paths (index p paths) d (commonVarAt paths p) i)))
checkPath (S fuel) ctx paths d (APLam body) (LArrow a b) = do
  (rest, MkAdmittedPathTerm ty w) <- checkPath fuel (a :: ctx) paths d body b
  Right (rest, MkAdmittedPathTerm (CPLamType ty) (HOPLambda ctx paths a b d w))
checkPath (S fuel) ctx paths d (APLam body) LUnit = Left TypeMismatch
checkPath (S fuel) ctx paths d (APLam body) LBool = Left TypeMismatch
checkPath (S fuel) ctx paths d (APApp a f x) b = do
  (rest, MkAdmittedPathTerm ft fw) <- checkPath fuel ctx paths d f (LArrow a b)
  (rest, MkAdmittedPathTerm xt xw) <- checkPath rest ctx paths d x a
  Right (rest, MkAdmittedPathTerm (CPAppType ft xt) (HOPApplication ctx paths a b d fw xw))
checkPath (S fuel) ctx paths d (APUnitElim x body) a = do
  (rest, MkAdmittedPathTerm xt xw) <- checkPath fuel ctx paths d x LUnit
  (rest, MkAdmittedPathTerm bt bw) <- checkPath rest ctx paths d body a
  Right (rest, MkAdmittedPathTerm (CPUnitElimType xt bt) (HOPUnitElim ctx paths a d xw bw))
checkPath (S fuel) ctx paths d (APIf c t f) a = do
  (rest, MkAdmittedPathTerm ct cw) <- checkPath fuel ctx paths d c LBool
  (rest, MkAdmittedPathTerm tt tw) <- checkPath rest ctx paths d t a
  (rest, MkAdmittedPathTerm ft fw) <- checkPath rest ctx paths d f a
  Right (rest, MkAdmittedPathTerm (CPIfType ct tt ft) (HOPIf ctx paths a d cw tw fw))

||| No derivation, semantic conclusion or context model is accepted as input.
public export
admitCommonTerm : AdmissionBudget -> (ctx : Vect n LogicalType) -> (raw : AdmissionTerm n) ->
  (a : LogicalType) -> Either AdmissionError (AdmittedTerm ctx raw a)
admitCommonTerm budget ctx raw a = do
  rest <- preflightContext (inputNodes budget) ctx
  rest <- preflightType rest a
  _ <- preflightTerm rest raw
  (_, evidence) <- checkTerm (checkingNodes budget) ctx raw a
  Right evidence

||| Contexts here specify only types and scope, NOT semantic admissibility of
||| declarations/endpoints. Equality and abstraction are outside this API.
public export
admitCommonPathTerm : AdmissionBudget -> (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) ->
  (d : Nat) -> (raw : AdmissionPathTerm n k d) -> (a : LogicalType) ->
  Either AdmissionError (AdmittedPathTerm ctx paths d raw a)
admitCommonPathTerm budget ctx paths d raw a = do
  rest <- preflightContext (inputNodes budget) ctx
  rest <- preflightContext rest paths
  rest <- preflightScope rest d
  rest <- preflightType rest a
  _ <- preflightPath rest raw
  (_, evidence) <- checkPath (checkingNodes budget) ctx paths d raw a
  Right evidence
