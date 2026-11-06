module Tests.FirstOrder

import Data.List
import Fibril.Termination.FirstOrder
import Fibril.Termination.SizeChange

%default total

isInvalid : Either Problem a -> Bool
isInvalid (Left (InvalidBody _)) = True
isInvalid _ = False

isExhausted : Either Problem a -> Bool
isExhausted (Left (AdmissionExhausted _)) = True
isExhausted _ = False

exhaustedWith : String -> Either Problem a -> Bool
exhaustedWith expected (Left (AdmissionExhausted actual)) = expected == actual
exhaustedWith _ _ = False

matches : List Function -> List Call -> Bool
matches program expected = case (extract program, check program expected) of
  (Right actual, Right ()) => actual == expected
  _ => False

||| End-to-end graph evidence for this synthetic fragment only.
abstractAccepted : List Function -> Bool
abstractAccepted program = case extract program of
  Left _ => False
  Right graph => case (check program graph, admittedArities program) of
    (Right (), Right sizes) => case produce sizes graph of
      ClosureProduced certificate GraphAccepted => case verify sizes graph certificate of
        GraphAccepted => True
        _ => False
      _ => False
    _ => False

boundProduction : List Function -> Bool
boundProduction program = case (extract program, admittedArities program) of
  (Right graph, Right sizes) => case produce sizes graph of
    ClosureProduced certificate GraphAccepted => case verifyBody program graph certificate of
      Right GraphAccepted => True
      _ => False
    _ => False
  _ => False

abstractRejected : List Function -> Bool
abstractRejected program = case extract program of
  Left _ => False
  Right graph => case (check program graph, admittedArities program) of
    (Right (), Right sizes) => case produce sizes graph of
      ClosureProduced _ (GraphRejected _) => True
      _ => False
    _ => False

calls : Nat -> Body
calls Z = End
calls (S Z) = Direct 0 [Local 0]
calls (S (S count)) = Both (Direct 0 [Local 0]) (calls (S count))

nested : Nat -> Body
nested Z = End
nested (S count) = CaseNat 0 End (nested count)

nestedLists : Nat -> Body
nestedLists Z = End
nestedLists (S count) = CaseList 0 End (nestedLists count)

aliases : Nat -> Body
aliases Z = End
aliases (S count) = LetLocal 0 (aliases count)

strictBody : List Function
strictBody = [Definition 1 (CaseNat 0 End (Direct 0 [Local 0]))]

weakBody : List Function
weakBody = [Definition 1 (Direct 0 [Local 0])]

public export
checks : List (String, Bool)
checks =
  [ ("first-order strict predecessor call extracts and checks its exact edge",
      matches strictBody [Edge 0 0 [[Decreases]]] && abstractAccepted strictBody)
  , ("first-order unchanged recursive argument is non-increasing, not strict",
      matches weakBody [Edge 0 0 [[NonIncreasing]]] && abstractRejected weakBody &&
      isInvalid (check weakBody [Edge 0 0 [[Decreases]]]))
  , ("first-order checker rejects omitted, extra and forged calls",
      isInvalid (check strictBody []) &&
      isInvalid (check strictBody [Edge 0 0 [[Decreases]], Edge 0 0 [[Decreases]]]) &&
      isInvalid (check strictBody [Edge 0 0 [[NonIncreasing]]]) &&
      isInvalid (check strictBody [Edge 0 1 [[Decreases]]]))
  , ("first-order branches use distinct scopes and retain both call sites",
      let program = [Definition 1 (CaseNat 0 (Direct 0 [Local 0]) (Direct 0 [Local 0]))]
          graph = [Edge 0 0 [[NonIncreasing]], Edge 0 0 [[Decreases]]] in
      matches program graph && abstractRejected program &&
      isInvalid (check program [Edge 0 0 [[Decreases]], Edge 0 0 [[Decreases]]]))
  , ("first-order zero branch cannot use the successor-only predecessor",
      let program = [Definition 1 (CaseNat 0 (Direct 0 [Local 1]) End)] in
      isInvalid (extract program) && isInvalid (check program [Edge 0 0 [[Decreases]]]))
  , ("first-order nested predecessor provenance survives shifts",
      let program = [Definition 2 (CaseNat 1 End (CaseNat 0 End (Direct 0 [Local 0, Local 2])))]
          graph = [Edge 0 0 [[Unknown, Decreases], [NonIncreasing, Unknown]]] in
      matches program graph)
  , ("first-order alternating arguments produce the expected closure",
      let program = [Definition 2 (CaseNat 1 End (Direct 0 [Local 0, Local 1]))]
          graph = [Edge 0 0 [[Unknown, Decreases], [NonIncreasing, Unknown]]] in
      matches program graph && abstractAccepted program)
  , ("first-order unrelated argument cannot forge decrease",
      let program = [Definition 1 (Direct 0 [Unrelated])]
          graph = [Edge 0 0 [[Unknown]]] in
      matches program graph && abstractRejected program &&
      isInvalid (check program [Edge 0 0 [[Decreases]]]))
  , ("first-order multiple syntactic calls are not deduplicated before checking",
      let program = [Definition 1 (Both (Direct 0 [Local 0]) (Direct 0 [Local 0]))]
          edge = Edge 0 0 [[NonIncreasing]] in
      matches program [edge, edge] && isInvalid (check program [edge]))
  , ("first-order alternatives preserve source traversal order",
      let program = [Definition 1 (Choice (Direct 0 [Local 0]) (Direct 0 [Unrelated]))]
          graph = [Edge 0 0 [[NonIncreasing]], Edge 0 0 [[Unknown]]] in
      matches program graph && isInvalid (check program (reverse graph)))
  , ("first-order mutual calls validate both bodies before closure",
      let program = [Definition 1 (CaseNat 0 End (Direct 1 [Local 0])), Definition 1 (Direct 0 [Local 0])]
          graph = [Edge 0 1 [[Decreases]], Edge 1 0 [[NonIncreasing]]] in
      matches program graph && abstractAccepted program && isInvalid (check program [Edge 0 1 [[Decreases]]]))
  , ("first-order malformed targets, arities and local indices fail closed",
      isInvalid (extract [Definition 1 (Direct 1 [Local 0])]) &&
      isInvalid (extract [Definition 1 (Direct 0 [])]) &&
      isInvalid (extract [Definition 1 (Direct 0 [Local 1])]) &&
      isInvalid (extract [Definition 1 (CaseNat 1 End End)]))
  , ("first-order call-site admission is checked independently of node admission",
      let exact = [Definition 1 (calls 128)]
          over = [Definition 1 (calls 65), Definition 1 (calls 64)] in
      case extract exact of
        Right graph => length graph == 128 && case check exact graph of
          Right () => exhaustedWith "call-site admission exhausted (128)" (extract over) &&
                      exhaustedWith "call-site admission exhausted (128)" (check over [])
          _ => False
        _ => False)
  , ("first-order body-node admission is checked independently of call admission",
      let exact = [Definition 1 (calls 127), Definition 1 (Both End End)]
          over = [Definition 1 (calls 128), Definition 1 End, Definition 1 End] in
      case extract exact of
        Right graph => length graph == 127 && case check exact graph of
          Right () => exhaustedWith "body-node admission exhausted (256)" (extract over) &&
                      exhaustedWith "body-node admission exhausted (256)" (check over [])
          _ => False
        _ => False)
  , ("first-order function and call arity maxima are admitted",
      let maximal = [Definition 8 (Direct 0 (map Local [0, 1, 2, 3, 4, 5, 6, 7]))] in
      case extract (replicate 16 (Definition 0 End)) of
        Right [] => case extract maximal of
          Right graph => case check maximal graph of Right () => True; _ => False
          _ => False
        _ => False)
  , ("first-order function, argument and local-scope admissions fail closed",
      case extract [Definition 8 (nested 8)] of
        Right _ => isExhausted (extract [Definition 8 (nested 9)]) &&
                   isExhausted (extract [Definition 9 End]) &&
                   isExhausted (extract (replicate 17 (Definition 0 End))) &&
                   isExhausted (extract [Definition 1 (Direct 0 (replicate 9 Unrelated))])
        _ => False)
  , ("first-order proposed graphs are bounded before matrix checking",
      isExhausted (check [] (replicate 129 (Edge 0 0 []))) &&
      isInvalid (check [Definition 1 (Direct 0 [Local 0])] [Edge 0 0 [replicate 9 Unknown]]))
  , ("first-order list tail is a strict descendant only in the cons branch",
      let program = [TypedDefinition [NatList] (CaseList 0 End (Direct 0 [Local 0]))]
          graph = [Edge 0 0 [[Decreases]]] in
      matches program graph && abstractAccepted program &&
      isInvalid (extract [TypedDefinition [NatList] (CaseList 0 (Direct 0 [Local 1]) End)]))
  , ("first-order nil branch retains the original list without inventing descent",
      let program = [TypedDefinition [NatList] (CaseList 0 (Direct 0 [Local 0]) End)]
          graph = [Edge 0 0 [[NonIncreasing]]] in
      matches program graph && abstractRejected program && isInvalid (check program [Edge 0 0 [[Decreases]]]))
  , ("first-order mixed Nat predecessor and list tail track separate roots",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (CaseNat 2 End (Direct 0 [Local 0, Local 1])))]
          graph = [Edge 0 0 [[Decreases, Unknown], [Unknown, Decreases]]] in
      matches program graph && abstractAccepted program)
  , ("first-order list head has no ordering relative to input Nat or list",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (Direct 0 [Local 1, Local 0]))]
          graph = [Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]]]
          forged = [Edge 0 0 [[Unknown, Decreases], [Unknown, Decreases]]] in
      matches program graph && abstractAccepted program && isInvalid (check program forged))
  , ("first-order predecessor of an unrelated head remains unrelated",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (CaseNat 1 End (Direct 0 [Local 0, Local 1])))]
          graph = [Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]]] in
      matches program graph && isInvalid (check program [Edge 0 0 [[Decreases, Unknown], [Unknown, Decreases]]]))
  , ("first-order replacing Nat by a head while keeping the list does not imply descent",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (Direct 0 [Local 1, Local 3]))]
          graph = [Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]]] in
      matches program graph && abstractRejected program)
  , ("first-order graph checking does not claim quantitative usage checking",
      let program = [TypedDefinition [NatList, NatList] (CaseList 0 End (Direct 0 [Local 0, Local 0]))]
          graph = [Edge 0 0 [[Decreases, Unknown], [Decreases, Unknown]]] in
      matches program graph && abstractAccepted program)
  , ("first-order cases and calls reject wrong synthetic sorts",
      let wrongNat = [TypedDefinition [NatList] (CaseNat 0 End End)]
          wrongList = [TypedDefinition [Natural] (CaseList 0 End End)]
          wrongCall = [TypedDefinition [NatList] (Direct 0 [Unrelated])]
          wrongLocal = [TypedDefinition [Natural, NatList] (Direct 0 [Local 1, Local 0])]
          wrongListValue = [TypedDefinition [Natural] (Direct 0 [UnrelatedList])] in
      isInvalid (extract wrongNat) && isInvalid (check wrongNat []) &&
      isInvalid (extract wrongList) && isInvalid (check wrongList []) &&
      isInvalid (extract wrongCall) && isInvalid (check wrongCall [Edge 0 0 [[Unknown]]]) &&
      isInvalid (extract wrongLocal) && isInvalid (check wrongLocal [Edge 0 0 [[Unknown, Unknown], [Unknown, Unknown]]]) &&
      isInvalid (extract wrongListValue) && isInvalid (check wrongListValue [Edge 0 0 [[Unknown]]]))
  , ("first-order mixed-sort mutual calls preserve target argument order",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (Direct 1 [Local 0, Local 1])),
                     TypedDefinition [NatList, Natural] (Direct 0 [Local 1, Local 0])]
          graph = [Edge 0 1 [[Unknown, Decreases], [Unknown, Unknown]],
                   Edge 1 0 [[Unknown, NonIncreasing], [NonIncreasing, Unknown]]] in
      matches program graph && abstractAccepted program && isInvalid (check program (reverse graph)))
  , ("first-order unrelated list values cannot forge tail descent",
      let program = [TypedDefinition [NatList] (Direct 0 [UnrelatedList])]
          graph = [Edge 0 0 [[Unknown]]] in
      matches program graph && abstractRejected program && isInvalid (check program [Edge 0 0 [[Decreases]]]))
  , ("first-order aliases preserve root provenance without inventing descent",
      let program = [Definition 1 (LetLocal 0 (Direct 0 [Local 0]))]
          graph = [Edge 0 0 [[NonIncreasing]]] in
      matches program graph && abstractRejected program && isInvalid (check program [Edge 0 0 [[Decreases]]]))
  , ("first-order aliases preserve actual predecessor and tail descent",
      let nat = [Definition 1 (CaseNat 0 End (LetLocal 0 (Direct 0 [Local 0])))]
          list = [TypedDefinition [NatList] (CaseList 0 End (LetLocal 0 (Direct 0 [Local 0])))]
          graph = [Edge 0 0 [[Decreases]]] in
      matches nat graph && abstractAccepted nat && boundProduction nat &&
      matches list graph && abstractAccepted list && boundProduction list)
  , ("first-order alias chains shift scopes without losing the original root",
      let program = [Definition 2 (CaseNat 1 End (LetLocal 0 (LetLocal 1 (Direct 0 [Local 0, Local 4]))))]
          graph = [Edge 0 0 [[Unknown, Decreases], [Unknown, NonIncreasing]]] in
      matches program graph && isInvalid (check program [Edge 0 0 [[Decreases, Unknown], [Unknown, NonIncreasing]]]))
  , ("first-order alias of an untracked list head remains unrelated",
      let program = [TypedDefinition [Natural, NatList] (CaseList 1 End (LetLocal 1 (Direct 0 [Local 0, Local 1])))]
          graph = [Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]]] in
      matches program graph && abstractAccepted program && isInvalid (check program [Edge 0 0 [[Decreases, Unknown], [Unknown, Decreases]]]))
  , ("first-order calls inside bindings cannot be omitted or added",
      let program = [Definition 1 (LetLocal 0 (Direct 0 [Local 0]))]
          edge = Edge 0 0 [[NonIncreasing]] in
      matches program [edge] && isInvalid (check program []) && isInvalid (check program [edge, edge]))
  , ("first-order body-bound certificates reject omitted or forged calls",
      let edge = Edge 0 0 [[Decreases]] in
      case verifyBody strictBody [edge] [edge] of
        Right GraphAccepted => isInvalid (verifyBody weakBody [edge] [edge]) &&
                               isInvalid (verifyBody strictBody [] [edge]) &&
                               isInvalid (verifyBody strictBody [edge, edge] [edge]) &&
                               isInvalid (verifyBody weakBody [edge] (replicate 33 edge))
        _ => False)
  , ("first-order body-bound certificate checks every duplicate call site",
      let program = [Definition 1 (CaseNat 0 End (Both (Direct 0 [Local 0]) (Direct 0 [Local 0])))]
          edge = Edge 0 0 [[Decreases]] in
      case verifyBody program [edge, edge] [edge] of
        Right GraphAccepted => isInvalid (verifyBody program [edge] [edge])
        _ => False)
  , ("first-order body-bound certificates retain rejection and exhaustion",
      let edge = Edge 0 0 [[Decreases]] in
      case verifyBody strictBody [edge] [] of
        Right (GraphRejected _) => isExhausted (verifyBody (replicate 17 (Definition 0 End)) [] []) &&
                                   case verifyBody strictBody [edge] (replicate 33 edge) of
                                     Right (GraphInconclusive _) => case verifyBody strictBody [edge] [edge, Edge 0 0 [[NonIncreasing]]] of
                                       Right (GraphRejected _) => True
                                       _ => False
                                     _ => False
        _ => False)
  , ("first-order alias scope is local to its body and preserves its sort",
      let leaked = [Definition 1 (Both (LetLocal 0 End) (Direct 0 [Local 1]))]
          wrongSort = [TypedDefinition [NatList] (LetLocal 0 (CaseNat 0 End End))]
          badAlias = [Definition 1 (LetLocal 1 End)] in
      isInvalid (extract leaked) && isInvalid (check leaked [Edge 0 0 [[Unknown]]]) &&
      isInvalid (extract wrongSort) && isInvalid (check wrongSort []) &&
      isInvalid (extract badAlias) && isInvalid (check badAlias []))
  , ("first-order opaque Nat predecessor and list tail remain unrelated",
      let nat = [Definition 1 (LetOpaque Natural (CaseNat 0 End (Direct 0 [Local 0])))]
          list = [TypedDefinition [NatList] (LetOpaque NatList (CaseList 0 End (Direct 0 [Local 0])))]
          unknown = [Edge 0 0 [[Unknown]]]
          forged = [Edge 0 0 [[Decreases]]] in
      matches nat unknown && abstractRejected nat && isInvalid (check nat forged) &&
      matches list unknown && abstractRejected list && isInvalid (check list forged))
  , ("first-order local alias and opaque binding honor scope admission",
      let exact = [Definition 8 (aliases 8)]
          over = [Definition 8 (aliases 9)]
          opaqueOver = [Definition 8 (LetOpaque Natural (aliases 8))] in
      case extract exact of
        Right graph => case check exact graph of
          Right () => exhaustedWith "local-scope admission exhausted (16)" (extract over) &&
                      exhaustedWith "local-scope admission exhausted (16)" (check over []) &&
                      exhaustedWith "local-scope admission exhausted (16)" (extract opaqueOver) &&
                      exhaustedWith "local-scope admission exhausted (16)" (check opaqueOver [])
          _ => False
        _ => False)
  , ("first-order typed sort and two-binder scope admissions are bounded",
      let scope15 = [TypedDefinition (replicate 8 NatList)
                      (CaseList 0 End (CaseList 0 End (CaseList 0 End (CaseNat 1 End (CaseList 1 End End)))))] in
      case extract [TypedDefinition (replicate 8 NatList) (nestedLists 4)] of
        Right graph => case check [TypedDefinition (replicate 8 NatList) (nestedLists 4)] graph of
          Right () => isExhausted (extract [TypedDefinition (replicate 8 NatList) (nestedLists 5)]) &&
                      isExhausted (check [TypedDefinition (replicate 8 NatList) (nestedLists 5)] []) &&
                      isExhausted (extract scope15) && isExhausted (check scope15 []) &&
                      isExhausted (extract [TypedDefinition (replicate 9 Natural) End]) &&
                      isExhausted (check [TypedDefinition (replicate 9 Natural) End] []) &&
                      isExhausted (admittedArities [TypedDefinition (replicate 9 Natural) End]) &&
                      isExhausted (admittedArities [Definition 9 End])
          _ => False
        _ => False)
  ]
