module Fibril.Cubical.Source.BoolCases

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term as C
import Fibril.Core.Reduction
import Fibril.Core.Quantitative.Syntax as Q
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Core.Quantitative.CoreTranslation

%default total

||| Exactly the first-order body grammar; no application or hidden conversion.
public export
data BoolBody = Input | Literal Bool | Conditional BoolBody BoolBody BoolBody

public export
embedBody : BoolBody -> Q.Term [BoolTy] BoolTy
embedBody Input = Ref Here
embedBody (Literal b) = Boolean b
embedBody (Conditional c t f) = If (embedBody c) (embedBody t) (embedBody f)

||| The allowance is shared across siblings and (by the caller) both endpoints.
public export
readBoolBody : Nat -> (term : Q.Term [BoolTy] BoolTy) ->
  Maybe (Nat, (body : BoolBody ** embedBody body = term))
readBoolBody Z _ = Nothing
readBoolBody (S fuel) (Ref Here) = Just (fuel, (Input ** Refl))
readBoolBody (S fuel) (Boolean b) = Just (fuel, (Literal b ** Refl))
readBoolBody (S fuel) (If c t f) = do
  (fuel, (cb ** Refl)) <- readBoolBody fuel c
  (fuel, (tb ** Refl)) <- readBoolBody fuel t
  (fuel, (fb ** Refl)) <- readBoolBody fuel f
  Just (fuel, (Conditional cb tb fb ** Refl))
readBoolBody _ _ = Nothing

public export
data BoolFunction : {0 a : Ty} -> Q.Term [] a -> Type where
  UnaryBool : (q : Quantity) -> (body : BoolBody) -> BoolFunction (Lam q (embedBody body))

public export
functionBody : BoolFunction term -> BoolBody
functionBody (UnaryBool q body) = body

public export
readBoolFunction : {a : Ty} -> Nat -> (term : Q.Term [] a) -> Maybe (Nat, BoolFunction term)
readBoolFunction fuel (Lam Erased body) = Nothing
readBoolFunction {a = Arrow q BoolTy BoolTy} fuel (Lam q body) = do
  (fuel, (b ** Refl)) <- readBoolBody fuel body
  Just (fuel, UnaryBool q b)
readBoolFunction _ _ = Nothing

public export
booleanCore : Bool -> C.Term n
booleanCore False = BoolFalse
booleanCore True = BoolTrue

public export
bodyCore : BoolBody -> C.Term 1
bodyCore Input = Variable FZ
bodyCore (Literal b) = booleanCore b
bodyCore (Conditional c t f) = BoolCase (bodyCore c) (bodyCore t) (bodyCore f)

public export
bodyCoreExact : (body : BoolBody) -> (ann : Annotations (embedBody body)) ->
  bodyCore body = coreTerm BoolTy (embedBody body) ann
bodyCoreExact Input ARef = Refl
bodyCoreExact (Literal False) ABoolean = Refl
bodyCoreExact (Literal True) ABoolean = Refl
bodyCoreExact (Conditional c t f) (AIf ca ta fa) =
  rewrite bodyCoreExact c ca in rewrite bodyCoreExact t ta in rewrite bodyCoreExact f fa in Refl

||| Closed Boolean computations used only for the operational proof.
public export
data GroundBool = Value Bool | Choice GroundBool GroundBool GroundBool

public export
closeBody : BoolBody -> Bool -> GroundBool
closeBody Input b = Value b
closeBody (Literal v) b = Value v
closeBody (Conditional c t f) b = Choice (closeBody c b) (closeBody t b) (closeBody f b)

public export
groundCore : GroundBool -> C.Term 0
groundCore (Value b) = booleanCore b
groundCore (Choice c t f) = BoolCase (groundCore c) (groundCore t) (groundCore f)

public export
chooseBool : Bool -> a -> a -> a
chooseBool False t f = f
chooseBool True t f = t

public export
evaluateGround : GroundBool -> Bool
evaluateGround (Value b) = b
evaluateGround (Choice c t f) = chooseBool (evaluateGround c) (evaluateGround t) (evaluateGround f)

public export
evaluateBody : BoolBody -> Bool -> Bool
evaluateBody body b = evaluateGround (closeBody body b)

public export
instantiateBody : (body : BoolBody) -> (b : Bool) ->
  instantiateTerm (booleanCore b) (bodyCore body) = groundCore (closeBody body b)
instantiateBody Input b = Refl
instantiateBody (Literal False) b = Refl
instantiateBody (Literal True) b = Refl
instantiateBody (Conditional c t f) b =
  rewrite instantiateBody c b in rewrite instantiateBody t b in rewrite instantiateBody f b in Refl

public export
data GroundStep : GroundBool -> GroundBool -> Type where
  SelectFalse : {t, f : GroundBool} -> GroundStep (Choice (Value False) t f) f
  SelectTrue : {t, f : GroundBool} -> GroundStep (Choice (Value True) t f) t
  InCondition : {c, next, t, f : GroundBool} -> GroundStep c next -> GroundStep (Choice c t f) (Choice next t f)

||| Every proof step is an actual contraction of the production reference reducer.
identityExact : (x : Identity a) -> Id (runIdentity x) = x
identityExact (Id x) = Refl

stepAction : {x, y : C.Term 0} -> step x = Just y ->
  stepWithGlobals {m = Identity} (const Nothing) x = Id (Just y)
stepAction {x} contraction = trans (sym (identityExact (stepWithGlobals {m = Identity} (const Nothing) x))) (cong Id contraction)

public export
groundStepSound : {c, next : GroundBool} -> GroundStep c next ->
  step (groundCore c) = Just (groundCore next)
groundStepSound SelectFalse = Refl
groundStepSound SelectTrue = Refl
groundStepSound (InCondition {c = Value b} s) impossible
groundStepSound (InCondition {c = Choice c t f} {next} s) =
  rewrite stepAction {x = groundCore (Choice c t f)} {y = groundCore next} (groundStepSound s) in Refl

public export
data GroundSteps : GroundBool -> GroundBool -> Type where
  Stay : {x : GroundBool} -> GroundSteps x x
  Next : {x, y, z : GroundBool} -> GroundStep x y -> GroundSteps y z -> GroundSteps x z

appendSteps : {x, y, z : GroundBool} -> GroundSteps x y -> GroundSteps y z -> GroundSteps x z
appendSteps Stay rest = rest
appendSteps (Next s ss) rest = Next s (appendSteps ss rest)

conditionSteps : {c, next, t, f : GroundBool} -> GroundSteps c next -> GroundSteps (Choice c t f) (Choice next t f)
conditionSteps Stay = Stay
conditionSteps (Next s ss) = Next (InCondition s) (conditionSteps ss)

public export
evaluateGroundReduces : (term : GroundBool) -> GroundSteps term (Value (evaluateGround term))
evaluateGroundReduces (Value b) = Stay
evaluateGroundReduces (Choice c t f) =
  appendSteps (conditionSteps (evaluateGroundReduces c)) (select (evaluateGround c))
  where
    select : (b : Bool) -> GroundSteps (Choice (Value b) t f)
      (Value (chooseBool b (evaluateGround t) (evaluateGround f)))
    select False = Next SelectFalse (evaluateGroundReduces f)
    select True = Next SelectTrue (evaluateGroundReduces t)

||| Reflexive transitive closure of the actual Core.Reduction.step, not a
||| parallel evaluator's unverified step relation.
public export
data CoreSteps : C.Term n -> C.Term n -> Type where
  CoreStay : CoreSteps x x
  CoreNext : {0 x, y, z : C.Term n} -> (0 contraction : step x = Just y) ->
    CoreSteps y z -> CoreSteps x z

public export
groundStepsSound : {x, y : GroundBool} -> GroundSteps x y -> CoreSteps (groundCore x) (groundCore y)
groundStepsSound Stay = CoreStay
groundStepsSound (Next s ss) = CoreNext (groundStepSound s) (groundStepsSound ss)

public export
booleanNormal : (b : Bool) -> step (the (C.Term 0) (booleanCore b)) = Nothing
booleanNormal False = Refl
booleanNormal True = Refl

public export
canonicalFunctionReduces : (q : Quantity) -> (body : BoolBody) -> (b : Bool) ->
  CoreSteps (Apply (Lambda q BoolType (bodyCore body)) (booleanCore b))
    (booleanCore (evaluateBody body b))
canonicalFunctionReduces q body b =
  CoreNext (cong Just (instantiateBody body b)) (groundStepsSound (evaluateGroundReduces (closeBody body b)))

||| This conclusion uses the supplied intrinsic term and its actual annotations.
public export
functionReduces : {a : Ty} -> {term : Q.Term [] a} ->
  (fun : BoolFunction term) -> (ann : Annotations term) -> (b : Bool) ->
  CoreSteps (Apply (coreTerm a term ann) (booleanCore b))
    (booleanCore (evaluateBody (functionBody fun) b))
functionReduces (UnaryBool q body) (ALam ann) b =
  rewrite sym (bodyCoreExact body ann) in canonicalFunctionReduces q body b

public export
record BoolAgreement (left, right : BoolBody) where
  constructor ByBoolCases
  falseAgreement : evaluateBody left False = evaluateBody right False
  trueAgreement : evaluateBody left True = evaluateBody right True

||| Exhaustive constructor elimination, not a finite collection of observations.
public export
boolAgreementAll : BoolAgreement left right -> (b : Bool) ->
  evaluateBody left b = evaluateBody right b
boolAgreementAll agreement False = agreement.falseAgreement
boolAgreementAll agreement True = agreement.trueAgreement

||| Both exact functions reduce to one normal form for EVERY Boolean input.
public export
boolAgreementOperational : {a, c : Ty} -> {left : Q.Term [] a} -> {right : Q.Term [] c} ->
  (lf : BoolFunction left) -> (rf : BoolFunction right) ->
  (la : Annotations left) -> (ra : Annotations right) ->
  BoolAgreement (functionBody lf) (functionBody rf) -> (b : Bool) ->
  (CoreSteps (Apply (coreTerm a left la) (booleanCore b)) (booleanCore (evaluateBody (functionBody lf) b)),
   CoreSteps (Apply (coreTerm c right ra) (booleanCore b)) (booleanCore (evaluateBody (functionBody lf) b)))
boolAgreementOperational lf rf la ra agreement b =
  (functionReduces lf la b,
   rewrite boolAgreementAll agreement b in functionReduces rf ra b)

public export
bodyTyping : (body : BoolBody) ->
  CommonHasType [LBool] (commonTerm (shadowTerm (embedBody body))) LBool
bodyTyping Input = CVariable LHere
bodyTyping (Literal b) = CBoolType
bodyTyping (Conditional c t f) = CConditionalType (bodyTyping c) (bodyTyping t) (bodyTyping f)

public export
bodyWitness : (body : BoolBody) -> HigherOrderTerm [LBool] LBool (bodyTyping body)
bodyWitness Input = HOVar [LBool] LBool LHere
bodyWitness (Literal b) = HOBool [LBool] b
bodyWitness (Conditional c t f) = HOIf [LBool] LBool (bodyWitness c) (bodyWitness t) (bodyWitness f)

chooseAgreement : (b : Bool) -> (t, f : Bool) -> commonChoose b t f = chooseBool b t f
chooseAgreement False t f = Refl
chooseAgreement True t f = Refl

public export
bodySemantics : (body : BoolBody) -> (b : Bool) ->
  applyMorphism (higherOrderTermSemantics (bodyWitness body)) (b, ()) = evaluateBody body b
bodySemantics Input b = Refl
bodySemantics (Literal v) b = Refl
bodySemantics (Conditional c t f) b =
  rewrite bodySemantics c b in rewrite bodySemantics t b in rewrite bodySemantics f b in
  chooseAgreement (evaluateBody c b) (evaluateBody t b) (evaluateBody f b)

public export
functionTyping : {a : Ty} -> {term : Q.Term [] a} -> (fun : BoolFunction term) ->
  CommonHasType [] (commonTerm (shadowTerm term)) (LArrow LBool LBool)
functionTyping (UnaryBool q body) = CLambdaType (bodyTyping body)

public export
functionWitness : {a : Ty} -> {term : Q.Term [] a} -> (fun : BoolFunction term) ->
  HigherOrderTerm [] (LArrow LBool LBool) (functionTyping fun)
functionWitness (UnaryBool q body) = HOLambda [] LBool LBool (bodyWitness body)

||| The selected higher-order setoid relation, on canonical witnesses for the
||| actual intrinsic syntax. No cross-syntax HigherOrderAlignment is assumed.
public export
boolAgreementSetoid : {a, c : Ty} -> {left : Q.Term [] a} -> {right : Q.Term [] c} ->
  (lf : BoolFunction left) -> (rf : BoolFunction right) ->
  BoolAgreement (functionBody lf) (functionBody rf) ->
  morphismsRelated (applyMorphism (higherOrderTermSemantics (functionWitness lf)) ())
    (applyMorphism (higherOrderTermSemantics (functionWitness rf)) ())
boolAgreementSetoid (UnaryBool q left) (UnaryBool r right) agreement x x Refl =
  trans (bodySemantics left x) (trans (boolAgreementAll agreement x) (sym (bodySemantics right x)))
