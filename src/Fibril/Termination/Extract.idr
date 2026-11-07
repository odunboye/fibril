-- Call extraction from a Fix body, for the size-change admission gate.
-- Untrusted producer: the verdict comes from SizeChange.produce/verify, and
-- unsupported syntax fails closed instead of being skipped.
module Fibril.Termination.Extract

import Data.Fin
import Data.List
import Fibril.Core.Pretty
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Termination.SizeChange

%default total

||| Number of leading function binders in a type.
public export
arityOf : Term n -> Nat
arityOf (Pi _ _ codomain) = S (arityOf codomain)
arityOf _ = 0

-- A row relates one value to the Fix function's original parameters.
Row : Type
Row = List Relation

unknownRow : Nat -> Row
unknownRow k = replicate k Unknown

upTo : Nat -> List Nat
upTo Z = []
upTo (S n) = upTo n ++ [n]

paramRow : Nat -> Nat -> Row
paramRow k j = map (\c => if c == j then NonIncreasing else Unknown) (upTo k)

-- Strictly smaller than something no larger than a parameter.
smaller : Relation -> Relation
smaller Unknown = Unknown
smaller NonIncreasing = Decreases
smaller Decreases = Decreases

-- Binders entered since the Fix are tracked newest first. The self variable
-- sits immediately outside them; anything beyond is an ordinary outer variable.
data Slot = Local Row | Partial (List Row) | SelfSlot | Outer

-- What a binder entered since the Fix stands for: a value related to the parameters by a
-- row, or an alias of a partial application of the recursive function itself (a let-bound
-- `f = self tag`), recorded by the rows of the arguments it already holds.
data Entry = Val Row | Alias (List Row)

slot : List Entry -> Fin m -> Slot
slot env i = go (finToNat i) env
  where
    go : Nat -> List Entry -> Slot
    go Z [] = SelfSlot
    go (S _) [] = Outer
    go Z (Val r :: _) = Local r
    go Z (Alias p :: _) = Partial p
    go (S d) (_ :: rs) = go d rs

argRow : Nat -> List Entry -> Term m -> Row
argRow k env (Variable i) = case slot env i of
  Local r => r
  _ => unknownRow k
argRow k _ _ = unknownRow k

tailRow : Nat -> List Entry -> Term m -> Row
tailRow k env (Variable i) = case slot env i of
  Local r => map smaller r
  _ => unknownRow k
tailRow k _ _ = unknownRow k

mutual
  walk : Nat -> List Entry -> Term m -> Either String (List Call)
  walk k env (Variable i) = case slot env i of
    SelfSlot => Left "the recursive function is used other than as the head of a saturated call"
    Partial _ => Left "the recursive function is used other than as the head of a saturated call"
    _ => Right []
  -- A global is closed and cannot contain this Fix's locally bound self.
  -- Typing validates its identity against an earlier acyclic environment before
  -- admission. No decrease is inferred from a global-headed result.
  walk k env (GlobalRef _) = Right []
  walk k env (Universe _) = Right []
  walk k env UnitType = Right []
  walk k env UnitValue = Right []
  walk k env BoolType = Right []
  walk k env BoolTrue = Right []
  walk k env BoolFalse = Right []
  walk k env NatType = Right []
  walk k env NatZero = Right []
  walk k env StringType = Right []
  walk k env (StringValue _) = Right []
  walk k env (RecType _) = Right []
  walk k env (NatSucc x) = walk k env x
  walk k env (StringAppend a b) = do x <- walk k env a; y <- walk k env b; Right (x ++ y)
  walk k env (StringEqual a b) = do x <- walk k env a; y <- walk k env b; Right (x ++ y)
  walk k env (UnitCase a b) = do x <- walk k env a; y <- walk k env b; Right (x ++ y)
  walk k env (BoolCase c y n) = do
    a <- walk k env c
    b <- walk k env y
    d <- walk k env n
    Right (a ++ b ++ d)
  walk k env (SeqType _ e) = walk k env e
  walk k env (SeqNil t) = walk k env t
  walk k env (SeqCons t h tl) = do
    a <- walk k env t
    b <- walk k env h
    c <- walk k env tl
    Right (a ++ b ++ c)
  walk k env (RecEnd t) = walk k env t
  walk k env (RecMore t v) = do x <- walk k env t; y <- walk k env v; Right (x ++ y)
  walk k env (PairValue t a b) = do
    x <- walk k env t
    y <- walk k env a
    z <- walk k env b
    Right (x ++ y ++ z)
  walk k env (PairCase m s b) = do
    x <- walk k env m
    y <- walk k env s
    z <- walk k env b
    Right (x ++ y ++ z)
  walk k env (Pi _ d b) = do
    x <- walk k env d
    y <- walk k (Val (unknownRow k) :: env) b
    Right (x ++ y)
  walk k env (Sigma _ _ d b) = do
    x <- walk k env d
    y <- walk k (Val (unknownRow k) :: env) b
    Right (x ++ y)
  -- A lambda away from the leading parameters may run later or repeatedly, so
  -- a call under it is not accounted for and is refused.
  walk k env (Lambda _ d b) = do
    x <- walk k env d
    y <- walk k (Val (unknownRow k) :: env) b
    case y of
      [] => Right x
      _ => Left "recursive call under a non-leading lambda"
  walk k env (SeqCase motive value base cons) = do
    a <- walk k env motive
    b <- walk k env value
    c <- walk k env base
    d <- walkCons k env (tailRow k env value) cons
    Right (a ++ b ++ c ++ d)
  -- Recursors and folds may be used (a helper inlined from a global), but not
  -- recursed through: the step is a lambda, so a self call inside it is refused
  -- below. Motive, base and value are ordinary evaluation positions.
  walk k env (NatRec motive base step value) = walk4 k env motive base step value
  walk k env (NatRecRuntime motive base step value) = walk4 k env motive base step value
  walk k env (RecFold motive base step value) = walk4 k env motive base step value
  walk k env (SeqFold motive base step value) = walk4 k env motive base step value
  walk k env (NatCase motive value base more) = do
    a <- walk k env motive
    b <- walk k env value
    c <- walk k env base
    d <- walkMore k env (tailRow k env value) more
    Right (a ++ b ++ c ++ d)
  walk k env (RecCase motive value base more) = do
    a <- walk k env motive
    b <- walk k env value
    c <- walk k env base
    d <- walkMore k env (tailRow k env value) more
    Right (a ++ b ++ c ++ d)
  -- A let (a lambda applied at once) runs its body once, in the same evaluation context, so
  -- calls inside it count. The bound variable inherits what is known about its value.
  walk k env (Apply (Lambda _ d inner) x) = do
    a <- walk k env d
    (entry, ex) <- entryOf k env x
    b <- walk k (entry :: env) inner
    Right (a ++ ex ++ b)
  walk k env (Apply f x) = do
    ex <- walk k env x
    walkApp k env f [argRow k env x] ex
  walk _ _ other = Left ("unsupported term form in a recursive body: " ++ pack (take 48 (unpack (renderTerm other))))

  -- The rows of a partial application of the recursive function (or of an alias to one),
  -- with the calls nested in its arguments; Nothing when the head is something else.
  aliasOf : Nat -> List Entry -> Term m -> Either String (Maybe (List Row, List Call))
  aliasOf k env (Variable i) = Right (case slot env i of
    SelfSlot => Just ([], [])
    Partial held => Just (held, [])
    _ => Nothing)
  aliasOf k env (Apply g y) = do
    inner <- aliasOf k env g
    case inner of
      Nothing => Right Nothing
      Just (rows, calls) => do
        ey <- walk k env y
        Right (Just (rows ++ [argRow k env y], calls ++ ey))
  aliasOf _ _ _ = Right Nothing

  -- What a let-bound value stands for: an alias of a not-yet-saturated call of the recursive
  -- function, the size relation of a variable it copies, or otherwise an unknown value.
  entryOf : Nat -> List Entry -> Term m -> Either String (Entry, List Call)
  entryOf k env x = do
    found <- aliasOf k env x
    case found of
      Just (rows, calls) =>
        if length rows < k then Right (Alias rows, calls) else other
      Nothing => other
    where
      unknown : Either String (Entry, List Call)
      unknown = do
        calls <- walk k env x
        Right (Val (unknownRow k), calls)
      other : Either String (Entry, List Call)
      other = case x of
        Variable i => case slot env i of
          Local r => Right (Val r, [])
          _ => unknown
        _ => unknown

  walk4 : Nat -> List Entry -> Term m -> Term m -> Term m -> Term m -> Either String (List Call)
  walk4 k env a b c d = do
    w <- walk k env a
    x <- walk k env b
    y <- walk k env c
    z <- walk k env d
    Right (w ++ x ++ y ++ z)

  -- The cons arm binds the head, then the tail as the newest variable.
  walkCons : Nat -> List Entry -> Row -> Term m -> Either String (List Call)
  walkCons k env tl (Lambda _ d1 (Lambda _ d2 inner)) = do
    x <- walk k env d1
    y <- walk k (Val (unknownRow k) :: env) d2
    z <- walk k (Val tl :: Val (unknownRow k) :: env) inner
    Right (x ++ y ++ z)
  walkCons k env _ other = walk k env other

  walkMore : Nat -> List Entry -> Row -> Term m -> Either String (List Call)
  walkMore k env tl (Lambda _ d inner) = do
    x <- walk k env d
    y <- walk k (Val tl :: env) inner
    Right (x ++ y)
  walkMore k env _ other = walk k env other

  -- Spine walk: arguments are collected as rows and also walked for nested calls.
  walkApp : Nat -> List Entry -> Term m -> List Row -> List Call -> Either String (List Call)
  walkApp k env (Apply g y) rows acc = do
    ey <- walk k env y
    walkApp k env g (argRow k env y :: rows) (acc ++ ey)
  walkApp k env (Variable i) rows acc = case slot env i of
    SelfSlot => if length rows == k then Right (Edge 0 0 rows :: acc)
                else Left "recursive call is not saturated"
    Partial held => if length held + length rows == k then Right (Edge 0 0 (held ++ rows) :: acc)
                      else Left "recursive call is not saturated"
    _ => Right acc
  walkApp k env other rows acc = do
    e <- walk k env other
    Right (acc ++ e)

-- The body must begin with one lambda per function argument in the type.
peel : Nat -> Nat -> List Entry -> Term m -> Either String (List Call)
peel k Z env body = walk k env body
peel k (S r) env (Lambda _ dom inner) = do
  x <- walk k env dom
  y <- peel k r (Val (paramRow k (minus k (S r))) :: env) inner
  Right (x ++ y)
peel _ _ _ _ = Left "recursive body has fewer leading lambdas than its type has arguments"

||| Extract one matrix per call site of the bound self in a Fix body. Matrices
||| are over the function's original parameters; Nothing is assumed about values
||| built by constructors, and only a case tail or predecessor can decrease.
public export
extractFix : Term n -> Term (S n) -> Either String (List Call)
extractFix ty body = case arityOf ty of
  Z => Left "recursive definition must have a function type"
  k => if k > 8 then Left "recursive definition has more than 8 arguments"
       else peel k k [] body

||| Preserve the extractor's supported closed-syntax boundary when a helper is
||| stored in a checked global environment instead of being embedded at its use.
||| Global references here are checked separately by the caller's acyclic walk.
public export
checkClosedGlobalSyntax : Term 0 -> Either String ()
checkClosedGlobalSyntax term = () <$ walk 0 [] term
