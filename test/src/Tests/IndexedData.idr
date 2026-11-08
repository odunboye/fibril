module Tests.IndexedData

import Data.Fin
import Data.List
import Fibril.Core.Context
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.Term

%default total

isRight : Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft : Either a b -> Bool
isLeft = not . isRight

vect : Term n -> Term n
vect n = Apply (Apply (DataType "Vect") StringType) n

nil : Term n
nil = Apply (DataCon "Vect" 0 1) StringType

cons : Term n -> Term n -> Term n -> Term n
cons n x xs = Apply (Apply (Apply (Apply (DataCon "Vect" 1 1) StringType) n) x) xs

vectDecl : DataDecl
vectDecl = IndexedDataDecl "Vect" (Field Erased (Universe 0) Done)
  (Field Erased NatType Done)
  [ IndexedConstructor "Nil" Done [NatZero]
  , IndexedConstructor "Cons"
      (Field Erased NatType
        (Field Unrestricted (Variable (FS FZ))
          (Field Unrestricted (Apply (Apply (DataType "Vect") (Variable (FS (FS FZ)))) (Variable (FS FZ))) Done)))
      [NatSucc (Variable (FS (FS FZ)))]
  ]

motive : Term n
motive = Lambda Erased NatType
  (Lambda Erased (vect (Variable FZ)) (vect (Variable (FS FZ))))

branch : Term n
branch = Lambda Erased NatType (Lambda Unrestricted StringType
  (Lambda Unrestricted (vect (Variable (FS FZ)))
    (cons (Variable (FS (FS FZ))) (Variable (FS FZ)) (Variable FZ))))

one : Term n
one = cons NatZero (StringValue "one") nil

withVect : (GlobalContext -> Bool) -> Bool
withVect test = case extendDataGlobals 512 1024 emptyGlobals vectDecl of
  Left _ => False
  Right globals => test globals

badIndex : DataDecl
badIndex = IndexedDataDecl "BadIndex" Done (Field Erased NatType Done)
  [IndexedConstructor "Bad" Done [BoolTrue]]

public export
checks : List (String, Bool)
checks =
  [ ("indexed Vect is admitted and its constructor types check", withVect (\_ => True))
  , ("Nil has length zero", withVect (\g => isRight (checkErasedGlobals g 512 1024 Empty nil (vect NatZero))))
  , ("Cons increases the length index", withVect (\g => isRight (checkErasedGlobals g 512 1024 Empty one (vect (NatSucc NatZero)))))
  , ("Nil cannot inhabit a nonempty vector", withVect (\g => isLeft (checkErasedGlobals g 512 1024 Empty nil (vect (NatSucc NatZero)))))
  , ("index-aware dependent case checks", withVect (\g => isRight (checkErasedGlobals g 512 1024 Empty
       (DataCase "Vect" motive one [nil, branch]) (vect (NatSucc NatZero)))))
  , ("dependent case checks the Nil branch at zero, not the scrutinee index", withVect (\g => isLeft
       (inferErasedGlobals g 512 1024 Empty (DataCase "Vect" motive one [one, branch]))))
  , ("an indexed motive cannot omit its index binder", withVect (\g => isLeft
       (inferErasedGlobals g 512 1024 Empty (DataCase "Vect" (Lambda Erased (vect NatZero) StringType) nil [StringValue "", branch]))))
  , ("constructor indices must have the declared index type", isLeft (extendDataGlobals 512 1024 emptyGlobals badIndex))
  , ("constructor indices must have the declared arity", isLeft (admitDeclaration
       (IndexedDataDecl "BadArity" Done (Field Erased NatType Done) [MkConstructor "Bad" Done])))
  , ("indices must be erased", isLeft (admitDeclaration
       (IndexedDataDecl "Relevant" Done (Field Unrestricted NatType Done) [IndexedConstructor "Bad" Done [NatZero]])))
  , ("recursive family occurrences under arrows remain forbidden", isLeft (admitDeclaration
       (IndexedDataDecl "Negative" Done (Field Erased NatType Done)
         [IndexedConstructor "Bad" (Field Unrestricted (Pi Unrestricted (Apply (DataType "Negative") NatZero) NatType) Done) [NatZero]])))
  , ("constructor result indices cannot mention the family", isLeft (admitDeclaration
       (IndexedDataDecl "SelfIndex" Done (Field Erased NatType Done) [IndexedConstructor "Bad" Done [DataType "SelfIndex"]])))
  ]
