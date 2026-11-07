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
data AdmissionError = InputLimit | CheckingLimit | TypeMismatch | SyntaxMismatch | UnsupportedEquality

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

||| First-order certificate syntax, not a target judgment or semantic proof.
||| Endpoint and restriction requests are retained for explicit fail-closed status.
public export
data AdmissionEquality : Nat -> Nat -> Nat -> Type where
  AERefl : AdmissionEquality n k d
  AESym : AdmissionEquality n k d -> AdmissionEquality n k d
  AETrans : AdmissionPathTerm n k d -> AdmissionEquality n k d -> AdmissionEquality n k d -> AdmissionEquality n k d
  AEApp : LogicalType -> AdmissionEquality n k d -> AdmissionEquality n k d -> AdmissionEquality n k d
  AEIf : AdmissionEquality n k d -> AdmissionEquality n k d -> AdmissionEquality n k d -> AdmissionEquality n k d
  AEUnitElim : AdmissionEquality n k d -> AdmissionEquality n k d -> AdmissionEquality n k d
  AEEndpoint : Fin k -> ScopedInterval d -> Bool -> AdmissionEquality n k d
  AERestrict : ScopedFace d -> AdmissionEquality n k d -> AdmissionEquality n k d

public export
data AdmissionDeclarations : Nat -> Nat -> Type where
  ADNil : AdmissionDeclarations n 0
  ADCons : LogicalType -> AdmissionTerm n -> AdmissionTerm n -> AdmissionDeclarations n k -> AdmissionDeclarations n (S k)

public export
admissionPathTypes : AdmissionDeclarations n k -> Vect k LogicalType
admissionPathTypes ADNil = []
admissionPathTypes (ADCons a _ _ rest) = a :: admissionPathTypes rest

||| Every raw endpoint has its own exact typing and computational witness.
public export
data AdmittedDeclarations : (ctx : Vect n LogicalType) -> (raw : AdmissionDeclarations n k) -> Type where
  CheckedNoPaths : AdmittedDeclarations ctx ADNil
  CheckedDeclare : AdmittedTerm ctx l a -> AdmittedTerm ctx r a -> AdmittedDeclarations ctx rest ->
    AdmittedDeclarations ctx (ADCons a l r rest)

public export
checkedDeclarations : {raw : AdmissionDeclarations n k} -> AdmittedDeclarations ctx raw -> CommonDeclarations ctx (admissionPathTypes raw)
checkedDeclarations CheckedNoPaths = CommonNoPaths
checkedDeclarations {raw = ADCons a left right remaining} (CheckedDeclare l r rest) =
  CommonDeclarePath (eraseAdmission left) (eraseAdmission right) (termTyping l) (termTyping r) (checkedDeclarations rest)

public export
record AdmittedEquality (ctx : Vect n LogicalType) (paths : Vect k LogicalType)
  (decls : CommonDeclarations ctx paths) (face : ScopedFace d)
  (left, right : AdmissionPathTerm n k d) (a : LogicalType) where
  constructor MkAdmittedEquality
  equalityLeft : AdmittedPathTerm ctx paths d left a
  equalityRight : AdmittedPathTerm ctx paths d right a
  faceEquality : CommonFaceEqual decls face (eraseAdmissionPath left) (eraseAdmissionPath right) a
  equalityEvidence : (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
    (adm : DependentPathAdmissible decls ps) ->
    DependentEndpointFaceEvidence faceEquality (pathWitness equalityLeft) (pathWitness equalityRight) ps adm

public export
record AdmittedEqualityInput (ctx : Vect n LogicalType) (raw : AdmissionDeclarations n k)
  (face : ScopedFace d) (left, right : AdmissionPathTerm n k d) (a : LogicalType) where
  constructor MkAdmittedEqualityInput
  admittedDeclarations : AdmittedDeclarations ctx raw
  admittedEquality : AdmittedEquality ctx (admissionPathTypes raw) (checkedDeclarations admittedDeclarations) face left right a

preflightFace : Nat -> ScopedFace d -> Either AdmissionError Nat
preflightFace fuel SBottom = spend fuel
preflightFace fuel STop = spend fuel
preflightFace fuel (SEndpoint i _) = spend fuel >>= (\rest => preflightIndex rest i)
preflightFace fuel (SConjunction x y) = do
  rest <- spend fuel
  rest <- preflightFace rest x
  preflightFace rest y
preflightFace fuel (SDisjunction x y) = do
  rest <- spend fuel
  rest <- preflightFace rest x
  preflightFace rest y

preflightDeclarations : Nat -> AdmissionDeclarations n k -> Either AdmissionError Nat
preflightDeclarations fuel ADNil = spend fuel
preflightDeclarations fuel (ADCons a l r rest) = do
  fuel <- spend fuel
  fuel <- preflightType fuel a
  fuel <- preflightTerm fuel l
  fuel <- preflightTerm fuel r
  preflightDeclarations fuel rest

preflightEquality : Nat -> AdmissionEquality n k d -> Either AdmissionError Nat
preflightEquality fuel AERefl = spend fuel
preflightEquality fuel (AESym c) = spend fuel >>= (\rest => preflightEquality rest c)
preflightEquality fuel (AETrans middle x y) = do
  rest <- spend fuel
  rest <- preflightPath rest middle
  rest <- preflightEquality rest x
  preflightEquality rest y
preflightEquality fuel (AEApp a f x) = do
  rest <- spend fuel
  rest <- preflightType rest a
  rest <- preflightEquality rest f
  preflightEquality rest x
preflightEquality fuel (AEIf c t f) = do
  rest <- spend fuel
  rest <- preflightEquality rest c
  rest <- preflightEquality rest t
  preflightEquality rest f
preflightEquality fuel (AEUnitElim x b) = do
  rest <- spend fuel
  rest <- preflightEquality rest x
  preflightEquality rest b
preflightEquality fuel (AEEndpoint p i _) = do
  rest <- spend fuel
  rest <- preflightIndex rest p
  preflightInterval rest i
preflightEquality fuel (AERestrict face c) = do
  rest <- spend fuel
  rest <- preflightFace rest face
  preflightEquality rest c

sameInterval : (x, y : ScopedInterval d) -> Maybe (x = y)
sameInterval Zero Zero = Just Refl
sameInterval One One = Just Refl
sameInterval (Var x) (Var y) = case decEq x y of
  Yes Refl => Just Refl
  No _ => Nothing
sameInterval (Reverse x) (Reverse y) = do
  Refl <- sameInterval x y
  Just Refl
sameInterval (Meet x y) (Meet z w) = do
  Refl <- sameInterval x z
  Refl <- sameInterval y w
  Just Refl
sameInterval (Join x y) (Join z w) = do
  Refl <- sameInterval x z
  Refl <- sameInterval y w
  Just Refl
sameInterval _ _ = Nothing

sameTerm : (x, y : AdmissionTerm n) -> Maybe (x = y)
sameTerm (AVar x) (AVar y) = case decEq x y of
  Yes Refl => Just Refl
  No _ => Nothing
sameTerm AUnit AUnit = Just Refl
sameTerm (ABool x) (ABool y) = case decEq x y of
  Yes Refl => Just Refl
  No _ => Nothing
sameTerm (ALam x) (ALam y) = do
  Refl <- sameTerm x y
  Just Refl
sameTerm (AApp a f x) (AApp b g y) = case commonTypeDecEq a b of
  No _ => Nothing
  Yes Refl => do
    Refl <- sameTerm f g
    Refl <- sameTerm x y
    Just Refl
sameTerm (AUnitElim x b) (AUnitElim y c) = do
  Refl <- sameTerm x y
  Refl <- sameTerm b c
  Just Refl
sameTerm (AIf c t f) (AIf c' t' f') = do
  Refl <- sameTerm c c'
  Refl <- sameTerm t t'
  Refl <- sameTerm f f'
  Just Refl
sameTerm _ _ = Nothing

samePath : (x, y : AdmissionPathTerm n k d) -> Maybe (x = y)
samePath (APOrdinary x) (APOrdinary y) = do
  Refl <- sameTerm x y
  Just Refl
samePath (APAt p i) (APAt q j) = case decEq p q of
  No _ => Nothing
  Yes Refl => do
    Refl <- sameInterval i j
    Just Refl
samePath (APLam x) (APLam y) = do
  Refl <- samePath x y
  Just Refl
samePath (APApp a f x) (APApp b g y) = case commonTypeDecEq a b of
  No _ => Nothing
  Yes Refl => do
    Refl <- samePath f g
    Refl <- samePath x y
    Just Refl
samePath (APUnitElim x b) (APUnitElim y c) = do
  Refl <- samePath x y
  Refl <- samePath b c
  Just Refl
samePath (APIf c t f) (APIf c' t' f') = do
  Refl <- samePath c c'
  Refl <- samePath t t'
  Refl <- samePath f f'
  Just Refl
samePath _ _ = Nothing

selfTermAlignment : (w : HigherOrderTerm ctx a ty) -> HigherOrderAlignment w w
selfTermAlignment (HOVar ctx a v) = AlignVar ctx a v
selfTermAlignment (HOUnit ctx) = AlignUnit ctx
selfTermAlignment (HOBool ctx b) = AlignBool ctx b
selfTermAlignment (HOLambda ctx a b w) = AlignLambda (selfTermAlignment w)
selfTermAlignment (HOApplication ctx a b f x) = AlignApplication (selfTermAlignment f) (selfTermAlignment x)
selfTermAlignment (HOUnitElim ctx a x b) = AlignUnitElim (selfTermAlignment x) (selfTermAlignment b)
selfTermAlignment (HOIf ctx a c t f) = AlignIf (selfTermAlignment c) (selfTermAlignment t) (selfTermAlignment f)

selfPathAlignment : (w : HigherOrderPathTerm ctx paths a d ty) -> HigherOrderPathAlignment w w
selfPathAlignment (HOPOrdinary ctx paths a d w) = AlignPathOrdinary (selfTermAlignment w)
selfPathAlignment (HOPAt ctx paths a d p i) = AlignPathAt ctx paths a d p i
selfPathAlignment (HOPLambda ctx paths a b d w) = AlignPathLambda (selfPathAlignment w)
selfPathAlignment (HOPApplication ctx paths a b d f x) = AlignPathApplication (selfPathAlignment f) (selfPathAlignment x)
selfPathAlignment (HOPUnitElim ctx paths a d x b) = AlignPathUnitElim (selfPathAlignment x) (selfPathAlignment b)
selfPathAlignment (HOPIf ctx paths a d c t f) = AlignPathIf (selfPathAlignment c) (selfPathAlignment t) (selfPathAlignment f)

checkDeclarations : Nat -> (ctx : Vect n LogicalType) -> (raw : AdmissionDeclarations n k) ->
  Either AdmissionError (Nat, AdmittedDeclarations ctx raw)
checkDeclarations Z ctx raw = Left CheckingLimit
checkDeclarations (S fuel) ctx ADNil = Right (fuel, CheckedNoPaths)
checkDeclarations (S fuel) ctx (ADCons a l r rest) = do
  (fuel, l') <- checkTerm fuel ctx l a
  (fuel, r') <- checkTerm fuel ctx r a
  (fuel, rest') <- checkDeclarations fuel ctx rest
  Right (fuel, CheckedDeclare l' r' rest')

||| Private checker invariant: this slice has no non-reflexive generators.
||| Sharing the SAME admitted witness avoids assuming coherence from erasure.
record CheckedReflexive (decls : CommonDeclarations ctx paths) (face : ScopedFace d)
  (raw : AdmissionPathTerm n k d) (a : LogicalType)
  (ty : CommonPathHasType ctx paths (eraseAdmissionPath raw) a)
  (w : HigherOrderPathTerm ctx paths a d ty) where
  constructor MkCheckedReflexive
  derivation : CommonFaceEqual decls face (eraseAdmissionPath raw) (eraseAdmissionPath raw) a
  structural : (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
    (adm : DependentPathAdmissible decls ps) -> DependentEndpointFaceEvidence derivation w w ps adm

checkReflexive : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {d : Nat} -> Nat -> (decls : CommonDeclarations ctx paths) -> (face : ScopedFace d) ->
  (raw : AdmissionPathTerm n k d) -> (a : LogicalType) ->
  (ty : CommonPathHasType ctx paths (eraseAdmissionPath raw) a) ->
  (w : HigherOrderPathTerm ctx paths a d ty) -> AdmissionEquality n k d ->
  Either AdmissionError (Nat, CheckedReflexive decls face raw a ty w)
checkReflexive Z decls face raw a ty w cert = Left CheckingLimit
checkReflexive (S fuel) decls face raw a ty w AERefl =
  Right (fuel, MkCheckedReflexive (CommonRefl ty)
    (\ps, adm => DepEndpointStructural (DepFaceRefl (selfPathAlignment w))))
checkReflexive (S fuel) decls face raw a ty w (AESym cert) = do
  (fuel, MkCheckedReflexive eq evidence) <- checkReflexive fuel decls face raw a ty w cert
  Right (fuel, MkCheckedReflexive (CommonSym eq) (\ps, adm => DepEndpointSym (evidence ps adm)))
checkReflexive (S fuel) decls face raw a ty w (AETrans middle c1 c2) = case samePath raw middle of
  Nothing => Left SyntaxMismatch
  Just Refl => do
    (fuel, MkCheckedReflexive eq1 e1) <- checkReflexive fuel decls face raw a ty w c1
    (fuel, MkCheckedReflexive eq2 e2) <- checkReflexive fuel decls face raw a ty w c2
    Right (fuel, MkCheckedReflexive (CommonTrans eq1 eq2)
      (\ps, adm => DepEndpointTrans (e1 ps adm) (selfPathAlignment w) (e2 ps adm)))
checkReflexive (S fuel) decls face (APApp domain f x) b
  (CPAppType ft xt) (HOPApplication ctx paths actual b d fw xw) (AEApp annotated cf cx) =
  case commonTypeDecEq domain annotated of
    No _ => Left TypeMismatch
    Yes Refl => case commonTypeDecEq actual domain of
      No _ => Left TypeMismatch
      Yes Refl => do
        (fuel, MkCheckedReflexive feq ef) <- checkReflexive fuel decls face f (LArrow actual b) ft fw cf
        (fuel, MkCheckedReflexive xeq ex) <- checkReflexive fuel decls face x actual xt xw cx
        Right (fuel, MkCheckedReflexive (CommonAppEqual feq xeq)
          (\ps, adm => DepEndpointApp (ef ps adm) (ex ps adm)))
checkReflexive (S fuel) decls face (APIf c t f) a (CPIfType ct tt ft)
  (HOPIf ctx paths a d cw tw fw) (AEIf cc tc fc) = do
    (fuel, MkCheckedReflexive ceq ec) <- checkReflexive fuel decls face c LBool ct cw cc
    (fuel, MkCheckedReflexive teq et) <- checkReflexive fuel decls face t a tt tw tc
    (fuel, MkCheckedReflexive feq ef) <- checkReflexive fuel decls face f a ft fw fc
    Right (fuel, MkCheckedReflexive (CommonIfEqual ceq teq feq)
      (\ps, adm => DepEndpointIf (ec ps adm) (et ps adm) (ef ps adm)))
checkReflexive (S fuel) decls face (APUnitElim x b) a (CPUnitElimType xt bt)
  (HOPUnitElim ctx paths a d xw bw) (AEUnitElim xc bc) = do
    (fuel, MkCheckedReflexive xeq ex) <- checkReflexive fuel decls face x LUnit xt xw xc
    (fuel, MkCheckedReflexive beq eb) <- checkReflexive fuel decls face b a bt bw bc
    Right (fuel, MkCheckedReflexive (CommonUnitElimEqual xeq beq)
      (\ps, adm => DepEndpointUnitElim (ex ps adm) (eb ps adm)))
checkReflexive (S fuel) decls face raw a ty w (AEEndpoint _ _ _) = Left UnsupportedEquality
checkReflexive (S fuel) decls face raw a ty w (AERestrict _ _) = Left UnsupportedEquality
checkReflexive (S fuel) decls face raw a ty w _ = Left SyntaxMismatch

unsupportedEquality : AdmissionEquality n k d -> Bool
unsupportedEquality AERefl = False
unsupportedEquality (AESym c) = unsupportedEquality c
unsupportedEquality (AETrans _ x y) = unsupportedEquality x || unsupportedEquality y
unsupportedEquality (AEApp _ f x) = unsupportedEquality f || unsupportedEquality x
unsupportedEquality (AEIf c t f) = unsupportedEquality c || unsupportedEquality t || unsupportedEquality f
unsupportedEquality (AEUnitElim x b) = unsupportedEquality x || unsupportedEquality b
unsupportedEquality (AEEndpoint _ _ _) = True
unsupportedEquality (AERestrict _ _) = True

||| All inputs are preflighted together before erasure, lookup or comparison.
||| No solver, substitution, evaluation or caller-supplied conclusion is used.
public export
admitCommonEquality : {d : Nat} -> AdmissionBudget -> (ctx : Vect n LogicalType) ->
  (raw : AdmissionDeclarations n k) -> (face : ScopedFace d) ->
  (left, right : AdmissionPathTerm n k d) -> (a : LogicalType) -> AdmissionEquality n k d ->
  Either AdmissionError (AdmittedEqualityInput ctx raw face left right a)
admitCommonEquality budget ctx raw face left right a cert = do
  fuel <- preflightContext (inputNodes budget) ctx
  fuel <- preflightDeclarations fuel raw
  fuel <- preflightScope fuel d
  fuel <- preflightFace fuel face
  fuel <- preflightPath fuel left
  fuel <- preflightPath fuel right
  fuel <- preflightType fuel a
  _ <- preflightEquality fuel cert
  if unsupportedEquality cert then Left UnsupportedEquality else Right ()
  (fuel, declarations) <- checkDeclarations (checkingNodes budget) ctx raw
  case samePath left right of
    Nothing => Left SyntaxMismatch
    Just Refl => do
      (fuel, typed) <- checkPath fuel ctx (admissionPathTypes raw) d left a
      (fuel, MkCheckedReflexive eq evidence) <- checkReflexive fuel (checkedDeclarations declarations) face left a
        (pathTyping typed) (pathWitness typed) cert
      Right (MkAdmittedEqualityInput declarations (MkAdmittedEquality typed typed eq evidence))
