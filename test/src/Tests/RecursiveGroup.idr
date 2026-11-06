module Tests.RecursiveGroup

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.RecursiveGroup
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
  ]
