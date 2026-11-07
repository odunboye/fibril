-- Runtime evaluation of closed terms, adding Fix unfolding to the reference reducer.
-- Type-level conversion keeps using Reduction/WeakHead, where Fix is neutral.
module Fibril.Core.Evaluation

import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.WeakHead

%default total

||| Head reduction that also unfolds Fix. Only for closed, checked runtime terms:
||| it never enters binders, so an open term stays stuck instead of unfolding forever.
public export
weakHeadRun : Nat -> Term n -> HeadResult n
weakHeadRun fuel term =
  case stepHeadWith True term of
    Nothing => HeadForm term
    Just next =>
      case fuel of
        Z => HeadLimit term
        S rest => weakHeadRun rest next

spineFix : Term n -> Bool
spineFix (Fix _ _) = True
spineFix (Apply function _) = spineFix function
spineFix _ = False

orElse : Maybe a -> Lazy (Maybe a) -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing other = other

-- One unfolding at a binder-free evaluation position of a closed term. Case
-- branches are binders, so they are reached only after a case fires and the
-- branch has been instantiated. Positions not listed here are left alone.
unfoldOne : Term 0 -> Maybe (Term 0)
unfoldOne (Apply function argument) =
  if spineFix function then stepHeadWith True (Apply function argument)
  else orElse (map (\f => Apply f argument) (unfoldOne function))
              (map (Apply function) (unfoldOne argument))
unfoldOne (NatSucc x) = map NatSucc (unfoldOne x)
unfoldOne (SeqCons ty head tail) =
  orElse (map (\h => SeqCons ty h tail) (unfoldOne head)) (map (SeqCons ty head) (unfoldOne tail))
unfoldOne (RecMore ty x) = map (RecMore ty) (unfoldOne x)
unfoldOne (PairValue ty a b) =
  orElse (map (\x => PairValue ty x b) (unfoldOne a)) (map (PairValue ty a) (unfoldOne b))
unfoldOne (NominalValue ty x) = map (NominalValue ty) (unfoldOne x)
unfoldOne (BoxValue ty x) = map (BoxValue ty) (unfoldOne x)
unfoldOne (VariantValue ty tag (Just x)) = map (VariantValue ty tag . Just) (unfoldOne x)
unfoldOne (IOPure x) = map IOPure (unfoldOne x)
unfoldOne (IOBind a b action next) = map (\x => IOBind a b x next) (unfoldOne action)
unfoldOne (StringAppend a b) =
  orElse (map (\x => StringAppend x b) (unfoldOne a)) (map (StringAppend a) (unfoldOne b))
unfoldOne (StringEqual a b) =
  orElse (map (\x => StringEqual x b) (unfoldOne a)) (map (StringEqual a) (unfoldOne b))
unfoldOne (BoolCase c yes no) = map (\x => BoolCase x yes no) (unfoldOne c)
unfoldOne (UnitCase s body) = map (\x => UnitCase x body) (unfoldOne s)
unfoldOne (SeqCase m v base cons) = map (\x => SeqCase m x base cons) (unfoldOne v)
unfoldOne (RecCase m v base more) = map (\x => RecCase m x base more) (unfoldOne v)
unfoldOne (NatRec m base next v) = map (NatRec m base next) (unfoldOne v)
unfoldOne (NatRecRuntime m base next v) = map (NatRecRuntime m base next) (unfoldOne v)
unfoldOne (SeqFold m base next v) = map (SeqFold m base next) (unfoldOne v)
unfoldOne (RecFold m base next v) = map (RecFold m base next) (unfoldOne v)
unfoldOne (PairCase m s branch) = map (\x => PairCase m x branch) (unfoldOne s)
unfoldOne (VariantCase m v branches) = map (\x => VariantCase m x branches) (unfoldOne v)
unfoldOne (NominalCase m v branch) = map (\x => NominalCase m x branch) (unfoldOne v)
unfoldOne (BoxCase m v branch) = map (\x => BoxCase m x branch) (unfoldOne v)
unfoldOne _ = Nothing

||| The reference step first; Fix is unfolded only once nothing else can reduce, so
||| Fix-free terms evaluate exactly as with `step`.
public export
stepRun : Term 0 -> Maybe (Term 0)
stepRun term = orElse (step term) (unfoldOne term)

||| Bounded evaluation of a closed term. Each unfolding costs one unit of fuel.
public export
normalizeRun : Nat -> Term 0 -> ReductionResult 0
normalizeRun fuel term =
  case stepRun term of
    Nothing => Normal term
    Just next =>
      case fuel of
        Z => OutOfFuel term
        S rest => normalizeRun rest next
