module Tests.RecursiveData

import Data.Fin
import Data.List
import Data.String
import Fibril.Core.Context
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Evaluation
import Fibril.Core.FixAdmission
import Fibril.Termination.Extract
import Fibril.Termination.SizeChange
import Fibril.Core.Pretty
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.Runtime
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
  , ("a recursive occurrence inside an intrinsic sequence is admitted",
      isRight (admitDeclaration (justOne (Field Unrestricted (SeqType "other" (DataType "T")) Done))))
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

-- Phase 3: typing against admitted declarations. ------------------------------------------

treeEnv : Either CheckError GlobalContext
treeEnv = extendDataGlobals 128 128 emptyGlobals treeDecl

bothEnv : Either CheckError GlobalContext
bothEnv = treeEnv >>= \g => extendDataGlobals 128 128 g listDecl

holds : Either CheckError GlobalContext -> (GlobalContext -> Bool) -> Bool
holds (Right g) f = f g
holds (Left _) _ = False

accepts : GlobalContext -> Term 0 -> Term 0 -> Bool
accepts g term ty = isRight (checkErasedGlobals g 128 128 Empty term ty)

rejects : GlobalContext -> Term 0 -> Term 0 -> Bool
rejects g term ty = isLeft (checkErasedGlobals g 128 128 Empty term ty)

natList : Term n
natList = Apply (DataType "List") NatType

-- Runtime usage: the same terms under quantity checking.
treeRuntime : Either RuntimeError RuntimeGlobals
treeRuntime = extendDataRuntimeGlobals 128 128 emptyRuntimeGlobals treeDecl

usageOk : Either RuntimeError RuntimeGlobals -> Term 0 -> Bool
usageOk (Right g) term = isRight (inferRuntimeGlobals g 128 128 Empty term)
usageOk (Left _) _ = False

usageRefused : Either RuntimeError RuntimeGlobals -> Term 0 -> Bool
usageRefused (Right g) term = isLeft (inferRuntimeGlobals g 128 128 Empty term)
usageRefused (Left _) _ = False

-- Rebuilds a node from its fields: each linear field used exactly once.
rebuildBranch : Term n
rebuildBranch = Lambda Linear tree (Lambda Linear tree (node (Variable (FS FZ)) (Variable FZ)))

treeMotive : Term n
treeMotive = Lambda Erased tree tree

rebuildCase : Term n -> Term n
rebuildCase scrutinee = DataCase "Tree" treeMotive scrutinee [leaf, rebuildBranch]

public export
typingChecks : List (String, Bool)
typingChecks =
  [ ("a binary tree family is admitted", isRight treeEnv)
  , ("a second family can be added after the first", isRight bothEnv)
  , ("adding a family twice is refused",
      holds treeEnv (\g => isLeft (extendDataGlobals 128 128 g treeDecl)))
  , ("a declaration failing positivity is refused at the typing layer",
      isLeft (extendDataGlobals 128 128 emptyGlobals
                (justOne (Field Unrestricted (Pi Unrestricted NatType (DataType "T")) Done))))
  , ("a field that is not a type is refused",
      isLeft (extendDataGlobals 128 128 emptyGlobals (justOne (Field Unrestricted NatZero Done))))
  , ("a field in Type 1 is refused: the family is declared in Type 0",
      isLeft (extendDataGlobals 128 128 emptyGlobals (justOne (Field Unrestricted (Universe 0) Done))))
  , ("a parameter may be a type of types",
      isRight (extendDataGlobals 128 128 emptyGlobals listDecl))
  , ("the family former has type Type 0",
      holds treeEnv (\g => accepts g tree (Universe 1) && accepts g tree (Universe 0)))
  , ("an unknown family has no type",
      holds treeEnv (\g => rejects g (DataType "Nope") (Universe 0)))
  , ("a parameterized family applied to its parameter is a type",
      holds bothEnv (\g => accepts g natList (Universe 0)))
  , ("a parameterized family needs its parameter",
      holds bothEnv (\g => rejects g (Apply (DataType "List") NatZero) (Universe 0)))
  , ("a leaf has the family type", holds treeEnv (\g => accepts g leaf tree))
  , ("a node of two trees has the family type", holds treeEnv (\g => accepts g (node leaf (node leaf leaf)) tree))
  , ("a node with a non-tree field is refused", holds treeEnv (\g => rejects g (node leaf NatZero) tree))
  , ("a constructor with the wrong parameter count is refused",
      holds treeEnv (\g => rejects g (DataCon "Tree" 0 1) tree))
  , ("a constructor index beyond the declaration is refused",
      holds treeEnv (\g => rejects g (DataCon "Tree" 2 0) tree))
  , ("a list cell takes its parameter, head and tail",
      holds bothEnv (\g => accepts g (listCons NatType NatZero (listNil NatType)) natList))
  , ("a list cell with a head of the wrong type is refused",
      holds bothEnv (\g => rejects g (listCons NatType BoolTrue (listNil NatType)) natList))
  , ("a list of one element type is not a list of another",
      holds bothEnv (\g => rejects g (listNil NatType) (Apply (DataType "List") BoolType)))
  , ("a case on a tree with matching branches has the motive's type",
      holds treeEnv (\g => accepts g (caseOf (node leaf leaf)) NatType))
  , ("a case reduces during checking: its type is the motive applied to the scrutinee",
      holds treeEnv (\g => accepts g (rebuildCase leaf) tree))
  , ("a case with a missing branch is refused",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) leaf [leafBranch]) NatType))
  , ("a case with an extra branch is refused",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) leaf [leafBranch, nodeBranch, leafBranch]) NatType))
  , ("a branch with the wrong field quantities is refused",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) leaf
                              [leafBranch, Lambda Unrestricted tree (Lambda Linear tree (NatSucc NatZero))]) NatType))
  , ("a branch whose result does not match the motive is refused",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) leaf [leafBranch, Lambda Linear tree (Lambda Linear tree BoolTrue)]) NatType))
  , ("a branch may use the fields, here rebuilding the node",
      holds treeEnv (\g => accepts g (rebuildCase (node leaf leaf)) tree))
  , ("a case needs an erased motive",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Linear tree NatType) leaf [leafBranch, nodeBranch]) NatType))
  , ("a case on the wrong family is refused",
      holds bothEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) (listNil NatType) [leafBranch, nodeBranch]) NatType))
  , ("a case on a non-data scrutinee is refused",
      holds treeEnv (\g => rejects g (DataCase "Tree" (Lambda Erased tree NatType) NatZero [leafBranch, nodeBranch]) NatType))
  , ("a case on an unknown family is refused",
      holds treeEnv (\g => rejects g (DataCase "Nope" (Lambda Erased tree NatType) leaf [leafBranch, nodeBranch]) NatType))
  , ("a list case skips the parameter and passes head and tail",
      holds bothEnv (\g => accepts g
        (DataCase "List" (Lambda Erased natList NatType) (listCons NatType NatZero (listNil NatType))
           [NatZero, Lambda Unrestricted NatType (Lambda Unrestricted natList (Variable (FS FZ)))])
        NatType))
  -- Runtime usage.
  , ("a linear branch that rebuilds from both fields passes the usage check",
      usageOk treeRuntime (rebuildCase (node leaf leaf)))
  , ("a linear branch that drops a linear field fails the usage check but not the erased one",
      usageRefused treeRuntime (caseOf (node leaf leaf)) && holds treeEnv (\g => accepts g (caseOf (node leaf leaf)) NatType))
  , ("a constructor application alone passes the usage check", usageOk treeRuntime (node leaf leaf))
  , ("the family former is a type, not a runtime value", usageRefused treeRuntime tree)
  ]

-- Phase 4: recursion. ------------------------------------------------------------------------

-- A copyable tree, so ordinary unrestricted recursion applies.
utree : Term n
utree = DataType "UTree"

uleaf : Term n
uleaf = DataCon "UTree" 0 0

unode : Term n -> Term n -> Term n
unode left right = Apply (Apply (DataCon "UTree" 1 0) left) right

utreeDecl : DataDecl
utreeDecl = MkDataDecl "UTree" Done
  [ MkConstructor "Leaf" Done
  , MkConstructor "Node" (Field Unrestricted (DataType "UTree") (Field Unrestricted (DataType "UTree") Done))
  ]

recursionEnv : Either CheckError GlobalContext
recursionEnv = extendDataGlobals 128 128 emptyGlobals utreeDecl >>= \g => extendDataGlobals 128 128 g listDecl

marksSig : Term 0
marksSig = Pi Unrestricted utree StringType

utreeMotive : Term n
utreeMotive = Lambda Erased utree StringType

-- Inside `\t =>`: t, self. Inside the node branch: right, left, t, self.
selfAt : Term n -> Term n
selfAt argument = argument

marksBody : Term 1
marksBody = Lambda Unrestricted utree
  (DataCase "UTree" utreeMotive (Variable FZ)
    [ StringValue "."
    , Lambda Unrestricted utree (Lambda Unrestricted utree
        (StringAppend (Apply (Variable (FS (FS (FS FZ)))) (Variable (FS FZ)))
                      (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ))))
    ])

marksFix : Term 0
marksFix = Fix marksSig marksBody

-- Recursion on a rebuilt node is not smaller.
rebuiltBody : Term 1
rebuiltBody = Lambda Unrestricted utree
  (DataCase "UTree" utreeMotive (Variable FZ)
    [ StringValue "."
    , Lambda Unrestricted utree (Lambda Unrestricted utree
        (Apply (Variable (FS (FS (FS FZ)))) (unode (Variable (FS FZ)) (Variable FZ))))
    ])

-- Recursion on the scrutinee itself is not smaller either.
sameBody : Term 1
sameBody = Lambda Unrestricted utree
  (DataCase "UTree" utreeMotive (Variable FZ)
    [ StringValue "."
    , Lambda Unrestricted utree (Lambda Unrestricted utree
        (Apply (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ)))))
    ])

-- A branch that returns a function: its extra lambda is not a field, so what it binds is
-- not a component of the scrutinee. Recursing on it must be refused.
functionMotive : Term n
functionMotive = Lambda Erased utree (Pi Unrestricted utree StringType)

extraLambdaBody : Term 1
extraLambdaBody = Lambda Unrestricted utree
  (Apply (DataCase "UTree" functionMotive (Variable FZ)
    [ Lambda Unrestricted utree (StringValue ".")
    , Lambda Unrestricted utree (Lambda Unrestricted utree (Lambda Unrestricted utree
        (Apply (Variable (FS (FS (FS (FS FZ))))) (Variable FZ))))
    ]) (Variable FZ))

-- Length of a list of naturals: the tail is a component, the head is not credited.
lengthSig : Term 0
lengthSig = Pi Unrestricted natList NatType

lengthBody : Term 1
lengthBody = Lambda Unrestricted natList
  (DataCase "List" (Lambda Erased natList NatType) (Variable FZ)
    [ NatZero
    , Lambda Unrestricted NatType (Lambda Unrestricted natList
        (NatSucc (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ))))
    ])

lengthFix : Term 0
lengthFix = Fix lengthSig lengthBody

twoLeaves : Term 0
twoLeaves = unode (unode uleaf uleaf) uleaf

public export
recursionChecks : List (String, Bool)
recursionChecks =
  [ ("structural recursion on both subtrees is admitted",
      holds recursionEnv (\g => isRight (inferErasedGlobals g 128 128 Empty marksFix)))
  , ("the extractor sees two recursive calls, each on a smaller component",
      case extractFixWith (fieldCountsOf (case recursionEnv of Right g => g; Left _ => emptyGlobals)) marksSig marksBody of
        Right found => length found.calls == 2 && all (\c => any (any (== Decreases)) c.matrix) found.calls
        Left _ => False)
  , ("without the declaration the extractor refuses a case on a family",
      isLeft (extractFix marksSig marksBody))
  , ("recursion on a rebuilt node is refused",
      holds recursionEnv (\g => isLeft (inferErasedGlobals g 128 128 Empty (Fix marksSig rebuiltBody))))
  , ("recursion on the scrutinee itself is refused",
      holds recursionEnv (\g => isLeft (inferErasedGlobals g 128 128 Empty (Fix marksSig sameBody))))
  , ("an extra lambda in a branch is not taken for a field",
      holds recursionEnv (\g => isLeft (inferErasedGlobals g 128 128 Empty (Fix marksSig extraLambdaBody))))
  , ("list length recursing on the tail is admitted",
      holds recursionEnv (\g => isRight (inferErasedGlobals g 128 128 Empty lengthFix)))
  , ("a recursive function over a family also passes runtime usage checking",
      usageOk (extendDataRuntimeGlobals 128 128 emptyRuntimeGlobals utreeDecl) marksFix)
  , ("run-mode evaluation unfolds the recursion through the case: three leaves make three dots",
      normalIs (normalizeRun 500 (Apply marksFix twoLeaves)) (StringValue "..."))
  , ("run-mode evaluation computes list length",
      normalIs (normalizeRun 500 (Apply lengthFix (listCons NatType NatZero (listCons NatType NatZero (listNil NatType)))))
               (NatSucc (NatSucc NatZero)))
  , ("a case on a leaf needs no unfolding",
      normalIs (normalizeRun 50 (Apply marksFix uleaf)) (StringValue "."))
  ]
