-- Stable diagnostic rendering of ordinary core syntax, not surface elaboration.
-- Nameless binding background: DEBRUIJN72; see docs/references.md.
module Fibril.Core.Pretty

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

mutual
  ||| Render explicit core syntax using newest-first variable indices.
  ||| Parentheses preserve tree structure; this is not accepted source syntax.
  ||| Output preserves annotations/quantities and does not evaluate terms.
  public export
  renderTerm : Term n -> String
  renderTerm (Variable i) = "v" ++ show (finToNat i)
  renderTerm (Universe level) = "Type" ++ show level
  renderTerm UnitType = "Unit"
  renderTerm UnitValue = "()"
  renderTerm BoolType = "Bool"
  renderTerm BoolTrue = "True"
  renderTerm BoolFalse = "False"
  renderTerm NatType = "Nat"
  renderTerm NatZero = "Zero"
  renderTerm (NatSucc x) = "(Succ " ++ renderTerm x ++ ")"
  renderTerm (NatRec p z s x) = "(NatRec " ++ renderTerm p ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ " " ++ renderTerm x ++ ")"
  renderTerm (NatRecRuntime p z s x) = "(NatRecRuntime " ++ renderTerm p ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ " " ++ renderTerm x ++ ")"
  renderTerm (RecType key) = "(RecType " ++ show key ++ ")"
  renderTerm (RecEnd ty) = "(RecEnd " ++ renderTerm ty ++ ")"
  renderTerm (RecMore ty x) = "(RecMore " ++ renderTerm ty ++ " " ++ renderTerm x ++ ")"
  renderTerm (RecFold p z s x) = "(RecFold " ++ renderTerm p ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ " " ++ renderTerm x ++ ")"
  renderTerm (RecCase p x z s) = "(RecCase " ++ renderTerm p ++ " " ++ renderTerm x ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ ")"
  renderTerm (NatCase p x z s) = "(NatCase " ++ renderTerm p ++ " " ++ renderTerm x ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ ")"
  renderTerm (SeqCase p x z s) = "(SeqCase " ++ renderTerm p ++ " " ++ renderTerm x ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ ")"
  renderTerm (SeqType key a) = "(SeqType " ++ show key ++ " " ++ renderTerm a ++ ")"
  renderTerm (SeqNil ty) = "(SeqNil " ++ renderTerm ty ++ ")"
  renderTerm (SeqCons ty h t) = "(SeqCons " ++ renderTerm ty ++ " " ++ renderTerm h ++ " " ++ renderTerm t ++ ")"
  renderTerm (SeqFold p z s x) = "(SeqFold " ++ renderTerm p ++ " " ++ renderTerm z ++ " " ++ renderTerm s ++ " " ++ renderTerm x ++ ")"
  renderTerm ReadLine = "ReadLine"
  renderTerm (FileHandleValue identity generation) = "(RuntimeFileHandle " ++ show identity ++ " " ++ show generation ++ ")"
  renderTerm (ReadInputFile handle) = "(ReadInputFile " ++ renderTerm handle ++ ")"
  renderTerm StringType = "String"
  renderTerm (StringValue value) = show value
  renderTerm (StringAppend left right) = "(StringAppend " ++ renderTerm left ++ " " ++ renderTerm right ++ ")"
  renderTerm (StringEqual left right) = "(StringEqual " ++ renderTerm left ++ " " ++ renderTerm right ++ ")"
  renderTerm (NominalType key indices shape) = "(Nominal " ++ show key ++ " [" ++ renderTerms indices ++ "] " ++ renderTerm shape ++ ")"
  renderTerm (NominalValue ty value) = "(NominalValue " ++ renderTerm ty ++ " " ++ renderTerm value ++ ")"
  renderTerm (NominalCase motive value branch) = "(NominalCase " ++ renderTerm motive ++ " " ++ renderTerm value ++ " " ++ renderTerm branch ++ ")"
  renderTerm (VariantType arms) = "(Variant " ++ renderArms arms ++ ")"
  renderTerm (VariantValue ty tag Nothing) = "(Inject " ++ renderTerm ty ++ " " ++ show tag ++ ")"
  renderTerm (VariantValue ty tag (Just value)) = "(Inject " ++ renderTerm ty ++ " " ++ show tag ++ " " ++ renderTerm value ++ ")"
  renderTerm (VariantCase motive value branches) = "(VariantCase " ++ renderTerm motive ++ " " ++ renderTerm value ++ " [" ++ renderTerms branches ++ "])"
  renderTerm (BoxType q ty) = "(Box " ++ show q ++ " " ++ renderTerm ty ++ ")"
  renderTerm (BoxValue ty value) = "(BoxValue " ++ renderTerm ty ++ " " ++ renderTerm value ++ ")"
  renderTerm (BoxCase motive value branch) = "(BoxCase " ++ renderTerm motive ++ " " ++ renderTerm value ++ " " ++ renderTerm branch ++ ")"
  renderTerm (WithInputFile result path body) = "(WithInputFile " ++ renderTerm result ++ " " ++ renderTerm path ++ " " ++ renderTerm body ++ ")"
  renderTerm (IOType ty) = "(IO " ++ renderTerm ty ++ ")"
  renderTerm (FileHandleType region) = "(FileHandle " ++ renderTerm region ++ ")"
  renderTerm (IOPure value) = "(Pure " ++ renderTerm value ++ ")"
  renderTerm (WriteLine text) = "(WriteLine " ++ renderTerm text ++ ")"
  renderTerm (IOBind a b action next) =
    "(Bind " ++ renderTerm a ++ " " ++ renderTerm b ++ " " ++ renderTerm action ++
    " " ++ renderTerm next ++ ")"
  renderTerm (BoolCase condition yes no) =
    "(If " ++ renderTerm condition ++ " " ++ renderTerm yes ++ " " ++ renderTerm no ++ ")"
  renderTerm (Sigma q r domain body) =
    "(Sigma " ++ show q ++ " " ++ show r ++ " " ++ renderTerm domain ++ " " ++ renderTerm body ++ ")"
  renderTerm (PairCase motive scrutinee branch) =
    "(PairCase " ++ renderTerm motive ++ " " ++ renderTerm scrutinee ++ " " ++ renderTerm branch ++ ")"
  renderTerm (PairValue ty first second) =
    "(Pair " ++ renderTerm ty ++ " " ++ renderTerm first ++ " " ++ renderTerm second ++ ")"
  renderTerm (Pi q domain body) =
    "(Pi " ++ show q ++ " " ++ renderTerm domain ++ " " ++ renderTerm body ++ ")"
  renderTerm (Lambda q domain body) =
    "(Lam " ++ show q ++ " " ++ renderTerm domain ++ " " ++ renderTerm body ++ ")"
  renderTerm (Fix ty body) =
    "(Fix " ++ renderTerm ty ++ " " ++ renderTerm body ++ ")"
  renderTerm (Apply function argument) =
    "(" ++ renderTerm function ++ " @ " ++ renderTerm argument ++ ")"

  renderTerm (UnitCase scrutinee body) =
    "(CaseUnit " ++ renderTerm scrutinee ++ " " ++ renderTerm body ++ ")"


  renderArms : List (Maybe (Quantity, Term n)) -> String
  renderArms [] = ""
  renderArms (Nothing :: rest) = " nullary" ++ renderArms rest
  renderArms (Just (q, ty) :: rest) = " (payload " ++ show q ++ " " ++ renderTerm ty ++ ")" ++ renderArms rest

  renderTerms : List (Term n) -> String
  renderTerms [] = ""
  renderTerms (value :: rest) = " " ++ renderTerm value ++ renderTerms rest

||| Shared representation for diagnostics, examples, and shrinking counterexamples.
public export
Show (Term n) where
  show = renderTerm
