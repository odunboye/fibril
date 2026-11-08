module Tests.RecursiveData

import Data.Fin
import Data.List
import Data.String
import Fibril.Core.Context
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Pretty
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.Size
import Fibril.Core.Term

%default total

-- Terms and reduction first, then the declaration admission rule.

tree : Term n
tree = DataType "Tree"

leaf : Term n
leaf = DataCon "Tree" 0 0

node : Term n -> Term n -> Term n
node left right = Apply (Apply (DataCon "Tree" 1 0) left) right

-- Zero for a leaf; one for any node, ignoring both subtrees.
leafBranch : Term n
leafBranch = NatZero

nodeBranch : Term n
nodeBranch = Lambda Linear tree (Lambda Linear tree (NatSucc NatZero))

caseOf : Term n -> Term n
caseOf scrutinee = DataCase "Tree" (Lambda Erased tree NatType) scrutinee [leafBranch, nodeBranch]

closedTree : Term 0
closedTree = tree

closedLeaf : Term 0
closedLeaf = leaf

closedCase : Term 0
closedCase = caseOf leaf

same0 : Term 0 -> Term 0 -> Bool
same0 = sameSyntax

closedBranch : Term 0
closedBranch = nodeBranch

closedMotive : Term 0
closedMotive = Lambda Erased tree NatType

normalIs : ReductionResult 0 -> Term 0 -> Bool
normalIs (Normal found) expected = sameSyntax found expected
normalIs _ _ = False

isLeft : Either e a -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either e a -> Bool
isRight (Right _) = True
isRight _ = False

-- A list over an erased element type: the leading argument is the parameter.
listCons : Term n -> Term n -> Term n -> Term n
listCons element head tail = Apply (Apply (Apply (DataCon "List" 1 1) element) head) tail

listNil : Term n -> Term n
listNil element = Apply (DataCon "List" 0 1) element

-- Declarations. Tree: no parameters; Node has two linear recursive fields.
treeDecl : DataDecl
treeDecl = MkDataDecl "Tree" Done
  [ MkConstructor "Leaf" Done
  , MkConstructor "Node" (Field Linear (DataType "Tree") (Field Linear (DataType "Tree") Done))
  ]

-- List A: the head is unrestricted, so the whole value is copyable. In the tail's scope the
-- parameter is the second variable, because the head came after it.
listDecl : DataDecl
listDecl = MkDataDecl "List" (Field Erased (Universe 0) Done)
  [ MkConstructor "Nil" Done
  , MkConstructor "Cons" (Field Unrestricted (Variable FZ) (Field Unrestricted (Apply (DataType "List") (Variable (FS FZ))) Done))
  ]

-- Two parameters. The first field has the first parameter's type; the recursive field is
-- given in the scope after it (three variables: both parameters and that field).
pairDecl : Term 3 -> DataDecl
pairDecl tailType = MkDataDecl "Both" (Field Erased (Universe 0) (Field Erased (Universe 0) Done))
  [ MkConstructor "Step" (Field Unrestricted (Variable (FS FZ)) (Field Unrestricted tailType Done)) ]

-- A single-constructor family with no parameters, for one field at a time.
justOne : Telescope 0 -> DataDecl
justOne fields = MkDataDecl "T" Done [ MkConstructor "C" fields ]

public export
checks : List (String, Bool)
checks =
  [ ("a case on a leaf takes the leaf branch", normalIs (normalize 64 (caseOf leaf)) NatZero)
  , ("a case on a node takes the node branch and applies it to the fields",
      normalIs (normalize 64 (caseOf (node leaf leaf))) (NatSucc NatZero))
  , ("the node branch receives its fields in order",
      normalIs (normalize 64 (DataCase "Tree" (Lambda Erased tree tree) (node leaf (node leaf leaf))
                  [leaf, Lambda Linear tree (Lambda Linear tree (Variable FZ))]))
               (node leaf leaf))
  , ("leading parameter arguments are not passed to the branch",
      normalIs (normalize 64 (DataCase "List" (Lambda Erased (Apply (DataType "List") NatType) NatType)
                  (listCons NatType NatZero (listNil NatType))
                  [NatZero, Lambda Unrestricted NatType (Lambda Unrestricted (Apply (DataType "List") NatType) (Variable (FS FZ)))]))
               NatZero)
  , ("a case on a variable is stuck",
      case normalize 64 (the (Term 1) (caseOf (Variable FZ))) of
        Normal found => sameSyntax found (caseOf (Variable FZ))
        _ => False)
  , ("a constructor of another family does not select a branch",
      case normalize 64 (the (Term 0) $ DataCase "Other" (Lambda Erased tree NatType) leaf [leafBranch, nodeBranch]) of
        Normal found => sameSyntax found (DataCase "Other" (Lambda Erased tree NatType) leaf [leafBranch, nodeBranch])
        _ => False)
  , ("a missing branch leaves the case stuck rather than crashing",
      case normalize 64 (the (Term 0) $ DataCase "Tree" (Lambda Erased tree NatType) (node leaf leaf) [leafBranch]) of
        Normal found => sameSyntax found (DataCase "Tree" (Lambda Erased tree NatType) (node leaf leaf) [leafBranch])
        _ => False)
  , ("reduction reaches the scrutinee through a redex",
      normalIs (normalize 64 (caseOf (Apply (Lambda Linear tree (Variable FZ)) leaf))) NatZero)
  , ("renaming shifts variables inside branches and the scrutinee",
      sameSyntax (rename (the (Fin 1 -> Fin 2) FS) (DataCase "Tree" (Lambda Erased tree NatType) (Variable FZ) [Variable FZ]))
                 (DataCase "Tree" (Lambda Erased tree NatType) (Variable (FS FZ)) [Variable (FS FZ)]))
  , ("substitution replaces variables in branches",
      sameSyntax (substituteTerm (\_ => NatZero) (the (Term 1) (DataCase "Tree" (Lambda Erased tree NatType) leaf [Variable FZ])))
                 (the (Term 0) (DataCase "Tree" (Lambda Erased tree NatType) leaf [NatZero])))
  , ("syntax equality distinguishes key, index and leading count",
      not (same0 (DataCon "A" 0 0) (DataCon "B" 0 0)) && not (same0 (DataCon "A" 0 0) (DataCon "A" 1 0))
      && not (same0 (DataCon "A" 0 0) (DataCon "A" 0 1)) && same0 (DataCon "A" 1 2) (DataCon "A" 1 2))
  , ("a case counts its motive, scrutinee, branches and one list cell per branch",
      coreNodes closedCase == 1 + coreNodes closedMotive + 1 + (1 + 1) + (1 + coreNodes closedBranch))
  , ("a family key is mentioned by its type, constructors and cases",
      mentionsNominal "Tree" closedTree && mentionsNominal "Tree" closedLeaf && mentionsNominal "Tree" closedCase
      && not (mentionsNominal "Other" closedCase))
  , ("terms render with their own constructor names",
      isPrefixOf "(DataType " (renderTerm closedTree) && isPrefixOf "(DataCon " (renderTerm closedLeaf)
      && isPrefixOf "(DataCase " (renderTerm closedCase))
  , ("typing refuses the new terms until its rules exist",
      isLeft (inferErased 64 64 Empty closedTree) && isLeft (inferErased 64 64 Empty closedLeaf)
      && isLeft (inferErased 64 64 Empty closedCase))
  -- Phase 2: admission.
  , ("a binary tree is admitted", isRight (admitDeclaration treeDecl))
  , ("a parameterized list with an unrestricted head is admitted", isRight (admitDeclaration listDecl))
  , ("two parameters used in order are admitted",
      isRight (admitDeclaration (pairDecl (Apply (Apply (DataType "Both") (Variable (FS (FS FZ)))) (Variable (FS FZ))))))
  , ("swapping the parameters in the recursive field is refused",
      isLeft (admitDeclaration (pairDecl (Apply (Apply (DataType "Both") (Variable (FS FZ))) (Variable (FS (FS FZ)))))))
  , ("changing a parameter in the recursive field is refused",
      isLeft (admitDeclaration (pairDecl (Apply (Apply (DataType "Both") NatType) (Variable (FS FZ))))))
  , ("dropping a parameter in the recursive field is refused",
      isLeft (admitDeclaration (pairDecl (Apply (DataType "Both") (Variable (FS (FS FZ)))))))
  , ("a recursive field under a function type is refused",
      isLeft (admitDeclaration (justOne (Field Unrestricted (Pi Unrestricted NatType (DataType "T")) Done))))
  , ("a recursive occurrence inside another type former is refused",
      isLeft (admitDeclaration (justOne (Field Unrestricted (SeqType "other" (DataType "T")) Done))))
  , ("a negative occurrence in a function domain is refused",
      isLeft (admitDeclaration (justOne (Field Unrestricted (Pi Unrestricted (DataType "T") NatType) Done))))
  , ("a plain non-recursive field is admitted",
      isRight (admitDeclaration (justOne (Field Unrestricted NatType Done))))
  , ("a later field may depend on an earlier recursive field's value",
      isRight (admitDeclaration (justOne (Field Unrestricted (DataType "T") (Field Unrestricted (Variable FZ) Done)))))
  , ("a mention of the family in a parameter type is refused",
      isLeft (admitDeclaration (MkDataDecl "T" (Field Erased (DataType "T") Done) [])))
  , ("a parameter must be erased",
      isLeft (admitDeclaration (MkDataDecl "T" (Field Unrestricted (Universe 0) Done) [])))
  , ("duplicate constructor names are refused",
      isLeft (admitDeclaration (MkDataDecl "T" Done [MkConstructor "C" Done, MkConstructor "C" Done])))
  , ("an empty constructor name is refused",
      isLeft (admitDeclaration (MkDataDecl "T" Done [MkConstructor "" Done])))
  , ("an empty key is refused", isLeft (admitDeclaration (MkDataDecl "" Done [])))
  , ("a family with no constructors is admitted", isRight (admitDeclaration (MkDataDecl "Void" Done [])))
  , ("more than the field cap is refused",
      isLeft (admitDeclaration (justOne (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType
        (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType
        (Field Unrestricted NatType (Field Unrestricted NatType Done))))))))))))
  , ("exactly the field cap is admitted",
      isRight (admitDeclaration (justOne (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType
        (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType (Field Unrestricted NatType
        (Field Unrestricted NatType Done)))))))))))
  , ("a refusal names the constructor and the field",
      case admitDeclaration (justOne (Field Unrestricted NatType (Field Unrestricted (Pi Unrestricted NatType (DataType "T")) Done))) of
        Left message => isInfixOf "constructor C, field 2" message
        Right () => False)
  ]
