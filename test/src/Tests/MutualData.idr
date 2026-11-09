module Tests.MutualData

import Data.List
import Fibril.Core.Context
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

isRight : Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft : Either a b -> Bool
isLeft = not . isRight

evenDecl : DataDecl
evenDecl = MkDataDecl "Even" Done
  [MkConstructor "ZeroEven" Done, MkConstructor "NextEven" (Field Unrestricted (DataType "Odd") Done)]

oddDecl : DataDecl
oddDecl = MkDataDecl "Odd" Done [MkConstructor "NextOdd" (Field Unrestricted (DataType "Even") Done)]

negative : DataDecl
negative = MkDataDecl "Negative" Done
  [MkConstructor "Bad" (Field Unrestricted (Pi Unrestricted (DataType "Other") NatType) Done)]

other : DataDecl
other = MkDataDecl "Other" Done [MkConstructor "Good" (Field Unrestricted (DataType "Negative") Done)]

public export
checks : List (String, Bool)
checks =
  [ ("positive nested mutual families are admitted atomically", isRight (extendDataGroupGlobals 512 512 emptyGlobals
       [MkDataDecl "A" Done [MkConstructor "MkA" (Field Linear (SeqType "Items" (DataType "B")) Done)],
        MkDataDecl "B" Done [MkConstructor "MkB" (Field Linear (DataType "A") Done)]]))
  , ("negative nested mutual partners are rejected", isLeft (admitGroup
       [MkDataDecl "A" Done [MkConstructor "MkA" (Field Linear (SeqType "Items" (Pi Linear (DataType "B") NatType)) Done)],
        MkDataDecl "B" Done [MkConstructor "MkB" (Field Linear (DataType "A") Done)]]))
  , ("positive mutual families are admitted atomically", isRight (extendDataGroupGlobals 512 512 emptyGlobals [evenDecl, oddDecl]))
  , ("a family cannot refer to an unregistered partner", isLeft (extendDataGlobals 512 512 emptyGlobals evenDecl))
  , ("a mutual constructor has the declared family type", case extendDataGroupGlobals 512 512 emptyGlobals [evenDecl, oddDecl] of
       Left _ => False
       Right globals => isRight (checkErasedGlobals globals 512 512 Empty
         (Apply (DataCon "Even" 1 0) (Apply (DataCon "Odd" 0 0) (DataCon "Even" 0 0))) (DataType "Even")))
  , ("negative recursion through a partner is rejected", isLeft (admitGroup [negative, other]))
  , ("duplicate group keys are rejected", isLeft (admitGroup [evenDecl, evenDecl]))
  , ("a one-family group is rejected", isLeft (admitGroup [evenDecl]))
  , ("re-registering a checked group is rejected", case extendDataGroupGlobals 512 512 emptyGlobals [evenDecl, oddDecl] of
       Left _ => False
       Right globals => isLeft (extendDataGroupGlobals 512 512 globals [evenDecl, oddDecl]))
  , ("group kind dependencies are rejected", isLeft (admitGroup
       [MkDataDecl "A" (Field Erased (DataType "B") Done) [], MkDataDecl "B" (Field Erased (DataType "B") Done) []]))
  , ("different parameter kinds are rejected", isLeft (admitGroup
       [MkDataDecl "A" (Field Erased (Universe 0) Done) [], MkDataDecl "B" (Field Erased NatType Done) []]))
  , ("unknown foreign field types are rejected", isLeft (extendDataGroupGlobals 512 512 emptyGlobals
       [MkDataDecl "A" Done [MkConstructor "MkA" (Field Unrestricted (DataType "Missing") Done)], MkDataDecl "B" Done []]))
  ]
