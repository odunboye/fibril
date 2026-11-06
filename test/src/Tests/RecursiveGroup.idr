module Tests.RecursiveGroup

import Data.Fin
import Data.Vect
import Fibril.Core.Context
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.RecursiveGroup
import Fibril.Core.RecursiveGroupCheck
import Fibril.Core.Term

%default total

-- Raw mutual bodies, not executable or checked as terminating definitions.
-- The only ordinary local at entry is the Nat parameter.
evenBody : Body [1, 1] 1
evenBody = CaseNat (Variable FZ) (Return BoolTrue) (Call (FS FZ) [Variable FZ])

oddBody : Body [1, 1] 1
oddBody = CaseNat (Variable FZ) (Return BoolFalse) (Call FZ [Variable FZ])

parity : Group 2
parity = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Linear NatType BoolType) evenBody)
    (MoreMembers (MkMember (Pi Linear NatType BoolType) oddBody) NoMembers))

-- A selected target determines the vector length, even when arities differ.
differentArities : Body [1, 2] 1
differentArities = Call (FS FZ) [Variable FZ, NatZero]

-- Idris must reject a call whose vector does not match the chosen target.
failing "Mismatch between"
  unsaturated : Body [1, 2] 1
  unsaturated = Call (FS FZ) [Variable FZ]

failing "Mismatch between"
  oversaturated : Body [1, 2] 1
  oversaturated = Call FZ [Variable FZ, NatZero]

failing "Mismatch between"
  outsideGroup : Body [1, 2] 1
  outsideGroup = Call (FS (FS FZ)) []

failing "Mismatch between"
  escapedLocal : Body [1] 1
  escapedLocal = Return (Variable (FS FZ))

emptyGroup : Group 0
emptyGroup = MkGroup [] NoMembers

-- Its arity table and signature intentionally disagree. Raw representation
-- must not be mistaken for a signature/arity or termination judgment.
malformedSignature : Group 1
malformedSignature = MkGroup [1] (MoreMembers (MkMember BoolType (Call FZ [Variable FZ])) NoMembers)

zeroArity : Group 2
zeroArity = MkGroup [0, 1]
  (MoreMembers (MkMember BoolType (Call (FS FZ) [NatZero]))
    (MoreMembers (MkMember (Pi Linear NatType BoolType) (Call FZ [])) NoMembers))

-- Includes both branch binders and an original outer local. This is scoped raw
-- syntax, not a claim that the argument types or case scrutinee are valid.
listBody : Body [3] 1
listBody = CaseList (Variable FZ) (Return NatZero)
  (Call FZ [Variable FZ, Variable (FS FZ), Variable (FS (FS FZ))])

boolBody : Body [1] 1
boolBody = CaseBool (Variable FZ) (Return (Variable FZ)) (Call FZ [Variable FZ])

closedSubstitution : Fin 1 -> Term 0
closedSubstitution _ = NatZero

accepted : Either e a -> Bool
accepted (Right _) = True
accepted _ = False

invalid : Either Problem a -> Bool
invalid (Left (Invalid _)) = True
invalid _ = False

unsupported : Either Problem a -> Bool
unsupported (Left (Unsupported _)) = True
unsupported _ = False

exhausted : Either Problem a -> Bool
exhausted (Left (Inconclusive _)) = True
exhausted _ = False

-- A fully saturated self-loop is well typed but emphatically not terminating.
loop : Group 1
loop = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType) (Call FZ [Variable FZ])) NoMembers)

wrongCall : Group 2
wrongCall = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Linear NatType BoolType) (Call (FS FZ) [Variable FZ]))
    (MoreMembers (MkMember (Pi Linear BoolType BoolType) (Return (Variable FZ))) NoMembers))

ordered : Group 2
ordered = MkGroup [2, 2]
  (MoreMembers (MkMember (Pi Linear NatType (Pi Linear BoolType BoolType))
    (Call (FS FZ) [Variable FZ, Variable (FS FZ)]))
   (MoreMembers (MkMember (Pi Linear BoolType (Pi Linear NatType BoolType))
    (CaseNat (Variable FZ) (Return (Variable (FS FZ)))
      (Call FZ [Variable FZ, Variable (FS (FS FZ))]))) NoMembers))

duplicateLinear : Group 1
duplicateLinear = MkGroup [2] (MoreMembers
  (MkMember (Pi Linear NatType (Pi Linear NatType NatType)) (Call FZ [Variable FZ, Variable FZ])) NoMembers)

twoBoolBody : Body [1, 2] 2
twoBoolBody = CaseBool (Variable FZ) (Return (Variable (FS FZ))) (Return (Variable (FS FZ)))

duplicateOnlyCall : Group 2
duplicateOnlyCall = MkGroup [1, 2]
  (MoreMembers (MkMember (Pi Linear BoolType BoolType) (Call (FS FZ) [Variable FZ, Variable FZ]))
    (MoreMembers (MkMember (Pi Linear BoolType (Pi Linear BoolType BoolType)) twoBoolBody) NoMembers))

singleValidCallee : Group 1
singleValidCallee = MkGroup [2] (MoreMembers
  (MkMember (Pi Linear BoolType (Pi Linear BoolType BoolType))
    (CaseBool (Variable FZ) (Return (Variable (FS FZ))) (Return (Variable (FS FZ))))) NoMembers)

erasedArguments : Group 2
erasedArguments = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Erased NatType BoolType) (Call (FS FZ) [Variable FZ]))
    (MoreMembers (MkMember (Pi Erased NatType BoolType) (Return BoolTrue)) NoMembers))

unrestrictedCall : Group 2
unrestrictedCall = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Linear NatType BoolType) (Call (FS FZ) [Variable FZ]))
    (MoreMembers (MkMember (Pi Unrestricted NatType BoolType) (Return BoolTrue)) NoMembers))

boolBranches : Bool -> Group 1
boolBranches usesBoth = MkGroup [2] (MoreMembers
  (MkMember (Pi Linear BoolType (Pi Linear BoolType BoolType))
    (CaseBool (Variable FZ) (Return (Variable (FS FZ)))
      (if usesBoth then Return (Variable (FS FZ)) else Return BoolFalse))) NoMembers)

natBranches : Bool -> Group 1
natBranches usesBoth = MkGroup [2] (MoreMembers
  (MkMember (Pi Linear NatType (Pi Linear BoolType BoolType))
    (CaseNat (Variable (FS FZ)) (Return (Variable FZ))
      (Call FZ [Variable FZ, if usesBoth then Variable (FS FZ) else BoolTrue]))) NoMembers)

manyMembers : (shape : Vect groupSize Nat) -> (remaining : Vect size Nat) -> Members shape remaining
manyMembers shape [] = NoMembers
manyMembers shape (_ :: rest) = MoreMembers (MkMember BoolType (Return BoolTrue)) (manyMembers shape rest)

manyGroups : (size : Nat) -> Group size
manyGroups size = MkGroup (replicate size 0) (manyMembers (replicate size 0) (replicate size 0))

natValue : Nat -> Term n
natValue Z = NatZero
natValue (S k) = NatSucc (natValue k)

sizedBody : Nat -> Group 1
sizedBody size = MkGroup [0] (MoreMembers (MkMember NatType (Return (natValue size))) NoMembers)

eightSignature : Term 0
eightSignature = Pi Linear NatType (Pi Unrestricted NatType (Pi Unrestricted NatType
  (Pi Unrestricted NatType (Pi Unrestricted NatType (Pi Unrestricted NatType
    (Pi Unrestricted NatType (Pi Unrestricted NatType BoolType)))))))

nestedNatCases : Nat -> Body [8] (S n)
nestedNatCases Z = Call FZ [Variable FZ, NatZero, NatZero, NatZero, NatZero, NatZero, NatZero, NatZero]
nestedNatCases (S k) = CaseNat (Variable FZ) (Return BoolTrue) (nestedNatCases k)

scopedCases : Nat -> Group 1
scopedCases depth = MkGroup [8] (MoreMembers (MkMember eightSignature
  (CaseNat (Variable (FS (FS (FS (FS (FS (FS (FS FZ)))))))) (Return BoolTrue) (nestedNatCases depth))) NoMembers)

public export
checks : List (String, Bool)
checks =
  [ ("recursive group stores separately scoped mutual call targets",
      case (memberAt parity FZ, memberAt parity (FS FZ)) of
        (MkMember evenType (CaseNat (Variable FZ) (Return BoolTrue) (Call (FS FZ) [Variable FZ])),
         MkMember oddType (CaseNat (Variable FZ) (Return BoolFalse) (Call FZ [Variable FZ]))) =>
          sameSyntax evenType (Pi Linear NatType BoolType) && sameSyntax evenType oddType
        _ => False)
  , ("recursive group call saturation follows the selected target arity",
      case differentArities of
        Call (FS FZ) [Variable FZ, NatZero] => True
        _ => False)
  , ("recursive group represents an empty raw group without admitting it",
      case emptyGroup of
        MkGroup [] NoMembers => True)
  , ("recursive group representation does not certify signatures or termination",
      case memberAt malformedSignature FZ of
        MkMember BoolType (Call FZ [Variable FZ]) => True
        _ => False)
  , ("recursive group permits zero-arity raw members and exact calls",
      case (memberAt zeroArity FZ, memberAt zeroArity (FS FZ)) of
        (MkMember _ (Call (FS FZ) [NatZero]), MkMember _ (Call FZ [])) => True
        _ => False)
  , ("recursive group renaming preserves predecessor and shifts outer locals",
      case renameBody FS evenBody of
        CaseNat (Variable (FS FZ)) (Return BoolTrue) (Call (FS FZ) [Variable FZ]) => True
        _ => False)
  , ("recursive group renaming preserves both list binders",
      case renameBody FS listBody of
        CaseList (Variable (FS FZ)) (Return NatZero)
          (Call FZ [Variable FZ, Variable (FS FZ), Variable (FS (FS (FS FZ)))]) => True
        _ => False)
  , ("recursive group substitution avoids capture under both list binders",
      case substituteBody closedSubstitution listBody of
        CaseList NatZero (Return NatZero) (Call FZ [Variable FZ, Variable (FS FZ), NatZero]) => True
        _ => False)
  , ("recursive group substitution visits condition and both Bool branches",
      case substituteBody closedSubstitution boolBody of
        CaseBool NatZero (Return NatZero) (Call FZ [NatZero]) => True
        _ => False)
  , ("recursive group substitution does not unfold calls",
      case substituteBody closedSubstitution evenBody of
        CaseNat NatZero (Return BoolTrue) (Call (FS FZ) [Variable FZ]) => True
        _ => False)
  , ("recursive group checker accepts the typed mutual Nat example",
      accepted (Fibril.Core.RecursiveGroupCheck.check parity))
  , ("recursive group checker does not claim termination",
      accepted (Fibril.Core.RecursiveGroupCheck.check loop))
  , ("recursive group checker validates nonempty groups and exact signature arity",
      invalid (Fibril.Core.RecursiveGroupCheck.check emptyGroup) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check malformedSignature) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType (Pi Linear NatType BoolType)) (Return BoolTrue)) NoMembers))))
  , ("recursive group checker validates argument types and telescope order",
      accepted (Fibril.Core.RecursiveGroupCheck.check ordered) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check wrongCall))
  , ("recursive group checker rejects wrong return and callee result types",
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType) (Return (Variable FZ))) NoMembers))) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [0, 0] (MoreMembers (MkMember BoolType (Call (FS FZ) []))
          (MoreMembers (MkMember NatType (Return NatZero)) NoMembers)))))
  , ("recursive group checker combines call argument usage",
      invalid (Fibril.Core.RecursiveGroupCheck.check duplicateLinear) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check unrestrictedCall) &&
      accepted (Fibril.Core.RecursiveGroupCheck.check erasedArguments))
  , ("recursive group checker rejects duplicating the sole linear call argument",
      accepted (Fibril.Core.RecursiveGroupCheck.check singleValidCallee) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check duplicateOnlyCall))
  , ("recursive group checker rejects reusing a case scrutinee in both branches",
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear BoolType BoolType)
          (CaseBool (Variable FZ) (Return (Variable FZ)) (Return (Variable FZ)))) NoMembers))))
  , ("recursive group checker joins exclusive Bool branches",
      accepted (Fibril.Core.RecursiveGroupCheck.check (boolBranches True)) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check (boolBranches False)))
  , ("recursive group Bool usage agrees with ordinary core on sampled cases",
      let goodTerm : Term 0 = Lambda Linear BoolType (BoolCase (Variable FZ) BoolTrue BoolFalse)
          badTerm : Term 0 = Lambda Linear BoolType (BoolCase (Variable FZ) (Variable FZ) (Variable FZ))
          goodGroup = MkGroup [1] (MoreMembers (MkMember (Pi Linear BoolType BoolType)
            (CaseBool (Variable FZ) (Return BoolTrue) (Return BoolFalse))) NoMembers)
          badGroup = MkGroup [1] (MoreMembers (MkMember (Pi Linear BoolType BoolType)
            (CaseBool (Variable FZ) (Return (Variable FZ)) (Return (Variable FZ)))) NoMembers) in
      accepted (inferRuntime 64 64 Empty goodTerm) && accepted (Fibril.Core.RecursiveGroupCheck.check goodGroup) &&
      not (accepted (inferRuntime 64 64 Empty badTerm)) && invalid (Fibril.Core.RecursiveGroupCheck.check badGroup))
  , ("recursive group checker respects erased and unrestricted case inputs",
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Erased BoolType BoolType)
          (CaseBool (Variable FZ) (Return BoolTrue) (Return BoolFalse))) NoMembers))) &&
      accepted (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Unrestricted BoolType BoolType)
          (CaseBool (Variable FZ) (Return (Variable FZ)) (Return (Variable FZ)))) NoMembers))))
  , ("recursive group checker joins Nat alternatives after predecessor discharge",
      accepted (Fibril.Core.RecursiveGroupCheck.check (natBranches True)) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check (natBranches False)))
  , ("recursive group checker validates case scrutinees and predecessor usage",
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
          (CaseNat (Variable FZ) (Return BoolTrue) (Return BoolFalse))) NoMembers))) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear BoolType BoolType)
          (CaseNat (Variable FZ) (Return BoolTrue) (Return (Variable FZ)))) NoMembers))))
  , ("recursive group checker rejects dependent and higher-order signatures",
      unsupported (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear (Pi Linear NatType NatType) BoolType) (Return BoolTrue)) NoMembers))) &&
      invalid (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType (Variable FZ)) (Return BoolTrue)) NoMembers))))
  , ("recursive group checker rejects unsupported effectful and list syntax",
      unsupported (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [0] (MoreMembers (MkMember BoolType (Return (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue))) NoMembers))) &&
      unsupported (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [0] (MoreMembers (MkMember BoolType (Return (IOPure BoolTrue))) NoMembers))) &&
      unsupported (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
          (CaseList (Variable FZ) (Return BoolTrue) (Return BoolFalse))) NoMembers))) &&
      unsupported (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [0, 1]
          (MoreMembers (MkMember BoolType (Call (FS FZ) [Apply (Lambda Linear NatType (Variable FZ)) NatZero]))
            (MoreMembers (MkMember (Pi Erased NatType BoolType) (Return BoolTrue)) NoMembers)))))
  , ("recursive group checker admits bounded member and body-node counts",
      accepted (Fibril.Core.RecursiveGroupCheck.check (manyGroups 16)) &&
      exhausted (Fibril.Core.RecursiveGroupCheck.check (manyGroups 17)) &&
      accepted (Fibril.Core.RecursiveGroupCheck.check (sizedBody 254)) &&
      exhausted (Fibril.Core.RecursiveGroupCheck.check (sizedBody 255)) &&
      exhausted (Fibril.Core.RecursiveGroupCheck.check
        (MkGroup [9] (MoreMembers (MkMember BoolType (Return BoolTrue)) NoMembers))))
  , ("recursive group checker admits exactly sixteen scoped locals",
      accepted (Fibril.Core.RecursiveGroupCheck.check (scopedCases 7)) &&
      exhausted (Fibril.Core.RecursiveGroupCheck.check (scopedCases 8)))
  ]
