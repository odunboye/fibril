module Tests.NestedData

import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

accepted : Either a b -> Bool
accepted (Right _) = True
accepted _ = False

rose : Term n
rose = DataType "Rose"

declaration : Term 0 -> DataDecl
declaration field = MkDataDecl "Rose" Done [MkConstructor "Node" (Field Linear field Done)]

public export
checks : List (String, Bool)
checks =
  [ ("nested sequence positivity is admitted", accepted (admitDeclaration (declaration (SeqType "Items" rose))))
  , ("multiple positive sequence layers are admitted", accepted (admitDeclaration (declaration (SeqType "Outer" (SeqType "Inner" rose)))))
  , ("sequence function-domain recursion is rejected", not (accepted (admitDeclaration (declaration (SeqType "Items" (Pi Linear rose NatType))))))
  , ("unknown container variance is rejected", not (accepted (admitDeclaration (declaration (Apply (DataType "Wrapper") rose)))))
  , ("nested family is checked by the ordinary core", accepted (extendDataGlobals 512 512 emptyGlobals (declaration (SeqType "Items" rose))))
  ]
