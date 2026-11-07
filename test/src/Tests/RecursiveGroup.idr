module Tests.RecursiveGroup

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.Renaming
import Fibril.Core.Size
import Fibril.Elaboration.MutualNat
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.RecursiveGroup
import Fibril.Core.RecursiveGroupCheck
import Fibril.Core.RecursiveGroupReference
import Fibril.Core.Term
import Fibril.Termination.GroupCalls
import Fibril.Termination.GroupCheck
import Fibril.Termination.SizeChange

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

mutatedParity : Group 2
mutatedParity = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Linear NatType BoolType) (Call (FS FZ) [Variable FZ]))
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

invalid : Either Fibril.Core.RecursiveGroupCheck.Problem a -> Bool
invalid (Left (Invalid _)) = True
invalid _ = False

unsupported : Either Fibril.Core.RecursiveGroupCheck.Problem a -> Bool
unsupported (Left (Fibril.Core.RecursiveGroupCheck.Unsupported _)) = True
unsupported _ = False

exhausted : Either Fibril.Core.RecursiveGroupCheck.Problem a -> Bool
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

alternativeCalls : Group 1
alternativeCalls = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
  (CaseNat (Variable FZ) (Call FZ [NatZero]) (Call FZ [Variable FZ]))) NoMembers)

nestedPredecessor : Group 1
nestedPredecessor = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
  (CaseNat (Variable FZ) (Return BoolTrue)
    (CaseNat (Variable FZ) (Return BoolFalse) (Call FZ [Variable FZ])))) NoMembers)

constructedScrutinee : Group 1
constructedScrutinee = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
  (CaseNat (NatSucc (Variable FZ)) (Return BoolTrue) (Call FZ [Variable FZ]))) NoMembers)

constructedArgument : Group 1
constructedArgument = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
  (CaseNat (Variable FZ) (Return BoolTrue) (Call FZ [NatSucc (Variable FZ)]))) NoMembers)

mixedArguments : Group 1
mixedArguments = MkGroup [2] (MoreMembers (MkMember (Pi Linear NatType (Pi Linear BoolType BoolType))
  (CaseNat (Variable (FS FZ)) (Return (Variable FZ))
    (Call FZ [Variable FZ, Variable (FS FZ)]))) NoMembers)

rectangular : Group 2
rectangular = MkGroup [1, 2]
  (MoreMembers (MkMember (Pi Linear NatType BoolType)
    (CaseNat (Variable FZ) (Return BoolTrue) (Call (FS FZ) [Variable FZ, BoolTrue])))
    (MoreMembers (MkMember (Pi Linear NatType (Pi Erased BoolType BoolType))
      (Call FZ [Variable (FS FZ)])) NoMembers))

rectangularLinear : Group 2
rectangularLinear = MkGroup [1, 2]
  (MoreMembers (MkMember (Pi Linear NatType BoolType)
    (CaseNat (Variable FZ) (Return BoolTrue) (Call (FS FZ) [Variable FZ, BoolTrue])))
    (MoreMembers (MkMember (Pi Linear NatType (Pi Linear BoolType BoolType))
      (CaseBool (Variable FZ) (Call FZ [Variable (FS FZ)]) (Call FZ [Variable (FS FZ)]))) NoMembers))

branchNot : Group 1
branchNot = MkGroup [1] (MoreMembers (MkMember (Pi Linear BoolType BoolType)
  (CaseBool (Variable FZ) (Return BoolFalse) (Return BoolTrue))) NoMembers)

constantBool : Group 1
constantBool = MkGroup [0] (MoreMembers (MkMember BoolType (Return BoolTrue)) NoMembers)

natIdentity : Group 1
natIdentity = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType NatType)
  (Return (Variable FZ))) NoMembers)

natGrowth : Group 1
natGrowth = MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType NatType)
  (Return (NatSucc (Variable FZ)))) NoMembers)

uncalledOmega : Group 2
uncalledOmega = MkGroup [0, 1] (MoreMembers (MkMember BoolType (Return BoolTrue))
  (MoreMembers (MkMember (Pi Unrestricted BoolType BoolType) (Return BoolTrue)) NoMembers))

omegaForward : Group 2
omegaForward = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Unrestricted BoolType BoolType) (Call (FS FZ) [Variable FZ]))
    (MoreMembers (MkMember (Pi Unrestricted BoolType BoolType)
      (CaseBool (Variable FZ) (Return (Variable FZ)) (Return (Variable FZ)))) NoMembers))

omegaStrict : Group 2
omegaStrict = MkGroup [1, 1]
  (MoreMembers (MkMember (Pi Unrestricted NatType BoolType) (Call (FS FZ) [NatSucc (Variable FZ)]))
    (MoreMembers (MkMember (Pi Unrestricted NatType BoolType) (Return BoolTrue)) NoMembers))

omegaRecursive : Group 1
omegaRecursive = MkGroup [2] (MoreMembers (MkMember (Pi Unrestricted BoolType (Pi Linear NatType BoolType))
  (CaseNat (Variable FZ) (Return (Variable (FS FZ)))
    (Call FZ [Variable (FS (FS FZ)), Variable FZ]))) NoMembers)

mixedUsage : Group 1
mixedUsage = MkGroup [2] (MoreMembers (MkMember (Pi Unrestricted BoolType (Pi Linear BoolType BoolType))
  (CaseBool (Variable (FS FZ)) (Return (Variable FZ))
    (CaseBool (Variable (FS FZ)) (Return (Variable FZ)) (Return (Variable FZ))))) NoMembers)

reference : Nat -> (group : Group size) -> (target : Fin size) ->
            Vect (index target group.arities) Value -> Maybe (Either Fibril.Core.RecursiveGroupReference.Problem Value)
reference fuel group target values = case Fibril.Termination.GroupCalls.extract group of
  Left _ => Nothing
  Right graph => case produce (toList group.arities) graph of
    ClosureProduced certificate GraphAccepted => Just (evaluate fuel group target values graph certificate)
    _ => Nothing

referenceIs : Nat -> (group : Group size) -> (target : Fin size) ->
              Vect (index target group.arities) Value -> Value -> Bool
referenceIs fuel group target values expected = case reference fuel group target values of
  Just (Right actual) => actual == expected
  _ => False

duplicateSites : Group 1
duplicateSites = MkGroup [2] (MoreMembers (MkMember (Pi Unrestricted BoolType (Pi Linear NatType NatType))
  (CaseBool (Variable (FS FZ)) (Call FZ [BoolTrue, Variable FZ]) (Call FZ [BoolTrue, Variable FZ]))) NoMembers)

matchesGraph : (group : Group size) -> List Call -> Bool
matchesGraph group expected = case Fibril.Termination.GroupCalls.extract group of
  Right actual => actual == expected && accepted (Fibril.Termination.GroupCheck.check group expected)
  _ => False

acceptedCertificate : (group : Group size) -> Bool
acceptedCertificate group = case Fibril.Termination.GroupCalls.extract group of
  Left _ => False
  Right graph => case produce (toList group.arities) graph of
    ClosureProduced certificate GraphAccepted => case Fibril.Termination.GroupCheck.verifyGroup group graph certificate of
      Right GraphAccepted => True
      _ => False
    _ => False

rejectedCertificate : (group : Group size) -> Bool
rejectedCertificate group = case Fibril.Termination.GroupCalls.extract group of
  Left _ => False
  Right graph => case produce (toList group.arities) graph of
    ClosureProduced certificate (GraphRejected _) => case Fibril.Termination.GroupCheck.verifyGroup group graph certificate of
      Right (GraphRejected _) => True
      _ => False
    _ => False

-- For every finite dispatch table, constructor equations hold on an OPEN
-- predecessor by existing beta/iota reduction, not merely sampled evaluation.
openEquation : Term 0 -> Term 0 -> Bool
openEquation entry target =
  case betaCompare 128 (the (Term 1) (Apply (weaken entry) (NatSucc (Variable FZ))))
                       (Apply (weaken target) (Variable FZ)) of
    EqualNormalForms => True
    _ => False

payloadBaseTerm : PayloadBase -> Term 2
payloadBaseTerm KeepPayload = Variable FZ
payloadBaseTerm (TruthTable yes no) = BoolCase (Variable FZ)
  (if yes then BoolTrue else BoolFalse) (if no then BoolTrue else BoolFalse)

payloadEquations : PayloadBase -> PayloadBase -> Bool -> Bool -> Bool
payloadEquations base0 base1 target0 target1 =
  let first = payloadWorker base0 base1 target0 target1 True
      second = payloadWorker base0 base1 target0 target1 False
      ty = Pi Linear NatType (Pi Linear BoolType BoolType)
   in accepted (checkRuntime 256 256 Empty first ty) && accepted (checkRuntime 256 256 Empty second ty) &&
      coreNodes first + coreNodes second + 2 * coreNodes ty <= 128 &&
      successor first (if target0 then first else second) &&
      successor second (if target1 then first else second) &&
      base first base0 && base second base1
  where
    successor : Term 0 -> Term 0 -> Bool
    successor entry target = case betaCompare 256
      (the (Term 2) (Apply (Apply (weaken (weaken entry)) (NatSucc (Variable (FS FZ)))) (Variable FZ)))
      (Apply (Apply (weaken (weaken target)) (Variable (FS FZ))) (Variable FZ)) of
        EqualNormalForms => True
        _ => False

    base : Term 0 -> PayloadBase -> Bool
    base entry plan = case betaCompare 256
      (the (Term 2) (Apply (Apply (weaken (weaken entry)) NatZero) (Variable FZ)))
      (payloadBaseTerm plan) of
        EqualNormalForms => True
        _ => False

payloadBases : List PayloadBase
payloadBases = [KeepPayload, TruthTable False False, TruthTable False True,
                TruthTable True False, TruthTable True True]

mutualEquations : Bool -> Bool -> Bool -> Bool -> Bool
mutualEquations base0 base1 target0 target1 =
  let first = worker base0 base1 target0 target1 True
      second = worker base0 base1 target0 target1 False
      ty = Pi Linear NatType BoolType
   in accepted (checkRuntime 256 256 Empty first ty) &&
      accepted (checkRuntime 256 256 Empty second ty) &&
      openEquation first (if target0 then first else second) &&
      openEquation second (if target1 then first else second)

public export
checks : List (String, Bool)
checks =
  [ ("payload lowering preserves open base/successor equations and quantities for all 100 plans",
      all (\base0 => all (\base1 => all (\target0 => all (payloadEquations base0 base1 target0)
        (the (List Bool) [False, True])) (the (List Bool) [False, True])) payloadBases) payloadBases)
  , ("payload template maximum fixed construction cost is exactly 120 nodes",
      let term = payloadWorker (TruthTable True False) (TruthTable False True) False True True in
      2 * coreNodes term + 2 * coreNodes (the (Term 0) (Pi Linear NatType (Pi Linear BoolType BoolType))) == 120)
  , ("mutual structural lowering checks and satisfies open successor equations for all tables",
      all (\base0 => all (\base1 => all (\target0 => all (mutualEquations base0 base1 target0)
        (the (List Bool) [False, True])) (the (List Bool) [False, True]))
        (the (List Bool) [False, True])) (the (List Bool) [False, True]))
  , ("recursive group stores separately scoped mutual call targets",
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
  , ("actual mutual group extracts and rechecks both decreasing calls",
      let calls = [Edge 0 1 [[Decreases]], Edge 1 0 [[Decreases]]] in
      matchesGraph parity calls && acceptedCertificate parity)
  , ("actual group tracks swapped arguments across mutually recursive members",
      let calls = [Edge 0 1 [[Unknown, NonIncreasing], [NonIncreasing, Unknown]],
                   Edge 1 0 [[Unknown, Decreases], [NonIncreasing, Unknown]]] in
      matchesGraph ordered calls && acceptedCertificate ordered)
  , ("actual group tracks rectangular calls across different arities",
      let calls = [Edge 0 1 [[Decreases], [Unknown]], Edge 1 0 [[NonIncreasing, Unknown]]] in
      matchesGraph rectangular calls && acceptedCertificate rectangular)
  , ("actual group self-loop is typed but its verified graph is rejected",
      matchesGraph loop [Edge 0 0 [[NonIncreasing]]] && rejectedCertificate loop)
  , ("actual group graph preserves alternative call sites and unknown constants",
      let calls = [Edge 0 0 [[Unknown]], Edge 0 0 [[Decreases]]] in
      matchesGraph alternativeCalls calls && rejectedCertificate alternativeCalls &&
      not (accepted (Fibril.Termination.GroupCheck.check alternativeCalls [Edge 0 0 [[Decreases]]])) &&
      not (accepted (Fibril.Termination.GroupCheck.check alternativeCalls (reverse calls))))
  , ("actual group tracks nested predecessors but not constructed values",
      matchesGraph nestedPredecessor [Edge 0 0 [[Decreases]]] && acceptedCertificate nestedPredecessor &&
      matchesGraph constructedScrutinee [Edge 0 0 [[Unknown]]] && rejectedCertificate constructedScrutinee &&
      matchesGraph constructedArgument [Edge 0 0 [[Unknown]]] && rejectedCertificate constructedArgument)
  , ("actual group mixed Nat and Bool provenance does not invent cross-sort descent",
      let edge = Edge 0 0 [[Decreases, Unknown], [Unknown, NonIncreasing]]
          forged = Edge 0 0 [[Decreases, Decreases], [Unknown, NonIncreasing]] in
      matchesGraph mixedArguments [edge] && acceptedCertificate mixedArguments &&
      not (accepted (Fibril.Termination.GroupCheck.check mixedArguments [forged])))
  , ("actual group certificate verifier rejects forged self-loop descent",
      let forged = Edge 0 0 [[Decreases]] in
      not (accepted (Fibril.Termination.GroupCheck.verifyGroup loop [forged] [forged])))
  , ("actual group graph recheck preserves duplicate site multiplicity",
      let edge = Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]] in
      matchesGraph duplicateSites [edge, edge] &&
      not (accepted (Fibril.Termination.GroupCheck.check duplicateSites [edge])))
  , ("actual group graph recheck rejects omitted, extra, stale and malformed edges",
      let calls = [Edge 0 1 [[Decreases]], Edge 1 0 [[Decreases]]]
          bad = [Edge 0 1 [[Decreases, Unknown]], Edge 1 0 [[Decreases]]]
          extra = calls ++ [Edge 0 1 [[Decreases]]] in
      not (accepted (Fibril.Termination.GroupCheck.check parity [])) &&
      not (accepted (Fibril.Termination.GroupCheck.check parity extra)) &&
      not (accepted (Fibril.Termination.GroupCheck.check parity bad)) &&
      not (accepted (Fibril.Termination.GroupCheck.check loop calls)) &&
      not (accepted (Fibril.Termination.GroupCheck.check parity [Edge 0 1 [[NonIncreasing]], Edge 1 0 [[Decreases]]])))
  , ("actual group certificate verification retains rejection and exhaustion",
      let calls = [Edge 0 1 [[Decreases]], Edge 1 0 [[Decreases]]] in
      case (Fibril.Termination.GroupCheck.verifyGroup parity calls [],
            Fibril.Termination.GroupCheck.verifyGroup parity calls (Data.List.replicate 33 (Edge 0 1 [[Decreases]])),
            Fibril.Termination.GroupCheck.check parity (Data.List.replicate 129 (Edge 0 1 [[Decreases]]))) of
        (Right (GraphRejected _), Right (GraphInconclusive _), Left (GraphAdmission _)) => True
        _ => False)
  , ("actual group graph paths preserve group admission exhaustion",
      case (Fibril.Termination.GroupCalls.extract (scopedCases 8),
            Fibril.Termination.GroupCheck.check (scopedCases 8) []) of
        (Left (Fibril.Termination.GroupCalls.GroupProblem (Inconclusive _)),
         Left (Fibril.Termination.GroupCheck.GroupProblem (Inconclusive _))) => True
        _ => False)
  , ("actual group extraction refuses malformed and unsupported groups",
      not (accepted (Fibril.Termination.GroupCalls.extract malformedSignature)) &&
      not (accepted (Fibril.Termination.GroupCheck.check malformedSignature [])) &&
      not (accepted (Fibril.Termination.GroupCalls.extract
        (MkGroup [1] (MoreMembers (MkMember (Pi Linear NatType BoolType)
          (CaseList (Variable FZ) (Return BoolTrue) (Return BoolFalse))) NoMembers)))))
  , ("group reference executes actual mutual parity for both members",
      referenceIs 20 parity FZ [Natural 0] (Boolean True) &&
      referenceIs 20 parity FZ [Natural 1] (Boolean False) &&
      referenceIs 20 parity FZ [Natural 2] (Boolean True) &&
      referenceIs 20 parity FZ [Natural 3] (Boolean False) &&
      referenceIs 20 parity (FS FZ) [Natural 0] (Boolean False) &&
      referenceIs 20 parity (FS FZ) [Natural 1] (Boolean True) &&
      referenceIs 20 parity (FS FZ) [Natural 2] (Boolean False) &&
      referenceIs 20 parity (FS FZ) [Natural 3] (Boolean True))
  , ("group reference respects swapped, rectangular and Bool-branch arguments",
      referenceIs 30 ordered FZ [Natural 2, Boolean False] (Boolean False) &&
      referenceIs 30 ordered (FS FZ) [Boolean True, Natural 2] (Boolean True) &&
      referenceIs 30 rectangularLinear FZ [Natural 2] (Boolean True) &&
      referenceIs 30 rectangularLinear (FS FZ) [Natural 2, Boolean False] (Boolean True) &&
      referenceIs 2 branchNot FZ [Boolean True] (Boolean False) &&
      referenceIs 2 branchNot FZ [Boolean False] (Boolean True) &&
      referenceIs 4 singleValidCallee FZ [Boolean True, Boolean False] (Boolean True) &&
      referenceIs 4 singleValidCallee FZ [Boolean False, Boolean True] (Boolean False))
  , ("group reference charges each actual body node exactly once",
      referenceIs 1 constantBool FZ [] (Boolean True) &&
      referenceIs 2 parity FZ [Natural 0] (Boolean True) &&
      referenceIs 4 parity FZ [Natural 1] (Boolean False) &&
      case (reference 0 constantBool FZ [], reference 1 parity FZ [Natural 0],
            reference 3 parity FZ [Natural 1]) of
        (Just (Left OutOfFuel), Just (Left OutOfFuel), Just (Left OutOfFuel)) => True
        _ => False)
  , ("group reference rejects wrong input types and caps Nat growth",
      referenceIs 2 natIdentity FZ [Natural 256] (Natural 256) &&
      referenceIs 2 natGrowth FZ [Natural 255] (Natural 256) &&
      case (reference 2 parity FZ [Boolean True], reference 2 natGrowth FZ [Natural 256],
            reference 2 parity FZ [Natural 257]) of
        (Just (Left (InvalidInput _)), Just (Left (AdmissionExhausted _)),
         Just (Left (AdmissionExhausted _))) => True
        _ => False)
  , ("group reference supports unrestricted values, forwarding and repeated reads",
      referenceIs 4 uncalledOmega FZ [] (Boolean True) &&
      referenceIs 4 uncalledOmega (FS FZ) [Boolean False] (Boolean True) &&
      referenceIs 4 omegaForward FZ [Boolean True] (Boolean True) &&
      referenceIs 4 omegaForward FZ [Boolean False] (Boolean False) &&
      referenceIs 4 omegaStrict FZ [Natural 255] (Boolean True) &&
      referenceIs 12 omegaRecursive FZ [Boolean False, Natural 3] (Boolean False) &&
      referenceIs 12 omegaRecursive FZ [Boolean True, Natural 3] (Boolean True) &&
      referenceIs 4 mixedUsage FZ [Boolean False, Boolean True] (Boolean True) &&
      referenceIs 4 mixedUsage FZ [Boolean True, Boolean False] (Boolean False))
  , ("group reference evaluates even unused unrestricted arguments strictly",
      case reference 4 omegaStrict FZ [Natural 256] of
        Just (Left (AdmissionExhausted _)) => True
        _ => False)
  , ("group reference still rejects erased parameters in any member",
      case reference 4 rectangular FZ [Natural 0] of
        Just (Left (Fibril.Core.RecursiveGroupReference.Unsupported _)) => True
        _ => False)
  , ("group reference rejects unrestricted calls that capture linear inputs",
      case evaluate 4 unrestrictedCall FZ [Natural 1] [] [] of
        Left (GraphFailure (Fibril.Termination.GroupCheck.GroupProblem (Invalid _))) => True
        _ => False)
  , ("group reference fuel policy has an explicit upper bound",
      referenceIs 4096 constantBool FZ [] (Boolean True) &&
      case reference 4097 constantBool FZ [] of
        Just (Left (AdmissionExhausted _)) => True
        _ => False)
  , ("group reference rejects evidence for a changed body with the same signatures",
      case Fibril.Termination.GroupCalls.extract parity of
        Right calls => case produce (toList parity.arities) calls of
          ClosureProduced certificate GraphAccepted =>
            case evaluate 20 mutatedParity FZ [Natural 2] calls certificate of
              Left (GraphFailure _) => True
              _ => False
          _ => False
        _ => False)
  , ("group reference authenticates calls and certificates before executing",
      let strict = Edge 0 0 [[Decreases]]
          calls = [Edge 0 1 [[Decreases]], Edge 1 0 [[Decreases]]] in
      (case (evaluate 0 loop FZ [Natural 0] [strict] [strict],
             evaluate 0 parity FZ [Natural 0] [] [],
             evaluate 0 parity FZ [Natural 0] calls []) of
        (Left (GraphFailure _), Left (GraphFailure _), Left (CertificateRejected _)) => True
        _ => False) &&
      (case (evaluate 0 parity FZ [Natural 0] calls (Data.List.replicate 33 strict),
             evaluate 0 loop FZ [Natural 0] [Edge 0 0 [[NonIncreasing]]] [Edge 0 0 [[NonIncreasing]]]) of
        (Left (CertificateInconclusive _), Left (CertificateRejected _)) => True
        _ => False))
  ]
