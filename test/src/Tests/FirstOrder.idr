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
  Right graph => case check program graph of
    Left _ => False
    Right () => case produce (map arity program) graph of
      ClosureProduced certificate GraphAccepted => case verify (map arity program) graph certificate of
        GraphAccepted => True
        _ => False
      _ => False

abstractRejected : List Function -> Bool
abstractRejected program = case extract program of
  Left _ => False
  Right graph => case check program graph of
    Left _ => False
    Right () => case produce (map arity program) graph of
      ClosureProduced _ (GraphRejected _) => True
      _ => False

calls : Nat -> Body
calls Z = End
calls (S Z) = Direct 0 [Local 0]
calls (S (S count)) = Both (Direct 0 [Local 0]) (calls (S count))

nested : Nat -> Body
nested Z = End
nested (S count) = CaseNat 0 End (nested count)

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
  ]
