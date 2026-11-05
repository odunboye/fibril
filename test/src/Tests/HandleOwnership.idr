module Tests.HandleOwnership

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Renaming
import Fibril.Core.Substitution
import Fibril.Core.Substitution.Composition
import Fibril.Driver.Check

%default total

accepted : String -> Bool
accepted source = case checkSource False source of
  Right _ => True
  Left _ => False

-- Require erased typing success so a syntax/type error cannot accidentally
-- masquerade as a successful resource-usage rejection.
usageRejected : String -> Bool
usageRejected source = case (checkSource True source, checkSource False source) of
  (Right _, Left _) => True
  _ => False

finish : String
finish = "\nmain : Unit\nmain = ()"

coreAccepted : Term 0 -> Term 0 -> Bool
coreAccepted term ty = case checkRuntime 512 128 Empty term ty of
  Right _ => True
  Left _ => False

handle : Term n
handle = FileHandleType UnitType

ownedResult : Term n
ownedResult = Sigma Linear Linear handle UnitType

public export
checks : List (String, Bool)
checks =
  [ ("handle type accepts a small region type",
      case inferErased 128 128 Empty (FileHandleType UnitType) of
        Right ty => sameSyntax ty (Universe 0)
        _ => False)
  , ("handle type rejects a higher-universe region",
      case inferErased 128 128 Empty (FileHandleType (Universe 0)) of
        Left _ => True
        _ => False)
  , ("handle type has no Unit value constructor",
      not (coreAccepted UnitValue handle))
  , ("handle ownership can be returned alongside a result",
      coreAccepted
        (Lambda Linear handle (IOPure (PairValue ownedResult (Variable FZ) UnitValue)))
        (Pi Linear handle (IOType ownedResult)))
  , ("handle cannot be both returned and packed as a second owner",
      not (coreAccepted
        (Lambda Linear handle
          (PairValue (Sigma Linear Linear handle handle) (Variable FZ) (Variable FZ)))
        (Pi Linear handle (Sigma Linear Linear handle handle))))
  , ("source abstract handle transfer is accepted",
      accepted ("move : (0 region : Type 0) -> (1 handle : FileHandle region) -> FileHandle region\nmove = \\(0 region : Type 0) => \\(1 handle : FileHandle region) => handle" ++ finish))
  , ("source abstract close consumes ownership once",
      accepted ("closeOwned : (0 region : Type 0) -> (closer : (1 file : FileHandle region) -> Unit) -> (1 handle : FileHandle region) -> Unit\ncloseOwned = \\(0 region : Type 0) => \\(closer : (1 file : FileHandle region) -> Unit) => \\(1 handle : FileHandle region) => closer handle" ++ finish))
  , ("source linear handle discard is a usage rejection",
      usageRejected ("drop : (0 region : Type 0) -> (1 handle : FileHandle region) -> Unit\ndrop = \\(0 region : Type 0) => \\(1 handle : FileHandle region) => ()" ++ finish))
  , ("source double abstract close is a usage rejection",
      usageRejected ("twice : (0 region : Type 0) -> (closer : (1 file : FileHandle region) -> Unit) -> (1 handle : FileHandle region) -> Unit\ntwice = \\(0 region : Type 0) => \\(closer : (1 file : FileHandle region) -> Unit) => \\(1 handle : FileHandle region) => case closer handle of () => closer handle" ++ finish))
  , ("source use after abstract close is a usage rejection",
      usageRejected ("after : (0 region : Type 0) -> (closer : (1 file : FileHandle region) -> Unit) -> (1 handle : FileHandle region) -> FileHandle region\nafter = \\(0 region : Type 0) => \\(closer : (1 file : FileHandle region) -> Unit) => \\(1 handle : FileHandle region) => case closer handle of () => handle" ++ finish))
  , ("source erased handle extraction is a usage rejection",
      usageRejected ("extract : (0 region : Type 0) -> (0 handle : FileHandle region) -> FileHandle region\nextract = \\(0 region : Type 0) => \\(0 handle : FileHandle region) => handle" ++ finish))
  , ("source unrestricted closure cannot capture a linear handle",
      usageRejected ("capture : (0 region : Type 0) -> (accept : (reader : (unit : Unit) -> FileHandle region) -> Unit) -> (1 handle : FileHandle region) -> Unit\ncapture = \\(0 region : Type 0) => \\(accept : (reader : (unit : Unit) -> FileHandle region) -> Unit) => \\(1 handle : FileHandle region) => accept (\\(unit : Unit) => handle)" ++ finish))
  , ("source cannot substitute a handle from a different abstract region",
      not (accepted ("cross : (0 left : Type 0) -> (0 right : Type 0) -> (1 handle : FileHandle left) -> FileHandle right\ncross = \\(0 left : Type 0) => \\(0 right : Type 0) => \\(1 handle : FileHandle left) => handle" ++ finish)))
  , ("source cannot forge a handle from Unit",
      not (accepted "main : FileHandle Unit\nmain = ()"))
  ]
