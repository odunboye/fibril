module Tests.SizeChange

import Data.List
import Fibril.Termination.SizeChange

%default total

relations : List Relation
relations = [Unknown, NonIncreasing, Decreases]

algebra : Bool
algebra = all (\a => all (\b => all (\c =>
  bestRelation a a == a &&
  bestRelation a b == bestRelation b a &&
  bestRelation (bestRelation a b) c == bestRelation a (bestRelation b c) &&
  composeRelation (composeRelation a b) c == composeRelation a (composeRelation b c) &&
  composeRelation a (bestRelation b c) == bestRelation (composeRelation a b) (composeRelation a c) &&
  composeRelation (bestRelation a b) c == bestRelation (composeRelation a c) (composeRelation b c)
  ) relations) relations) relations

accepted : Verdict -> Bool
accepted GraphAccepted = True
accepted _ = False

rejected : Verdict -> Bool
rejected (GraphRejected _) = True
rejected _ = False

inconclusive : Verdict -> Bool
inconclusive (GraphInconclusive _) = True
inconclusive _ = False

strict : Call
strict = Edge 0 0 [[Decreases]]

weak : Call
weak = Edge 0 0 [[NonIncreasing]]

unknown : Call
unknown = Edge 0 0 [[Unknown]]

-- The alternating argument descent becomes strict on the diagonal only after
-- composition. A separate off-diagonal strict matrix is also in the closure.
swapDescending : Call
swapDescending = Edge 0 0 [[Unknown, Decreases], [NonIncreasing, Unknown]]

strictDiagonal2 : Call
strictDiagonal2 = Edge 0 0 [[Decreases, Unknown], [Unknown, Decreases]]

strictSwap : Call
strictSwap = Edge 0 0 [[Unknown, Decreases], [Decreases, Unknown]]

weakSwap : Call
weakSwap = Edge 0 0 [[Unknown, NonIncreasing], [NonIncreasing, Unknown]]

weakDiagonal2 : Call
weakDiagonal2 = Edge 0 0 [[NonIncreasing, Unknown], [Unknown, NonIncreasing]]

sameVerdict : Verdict -> Verdict -> Bool
sameVerdict GraphAccepted GraphAccepted = True
sameVerdict (GraphRejected a) (GraphRejected b) = a == b
sameVerdict (GraphInconclusive a) (GraphInconclusive b) = a == b
sameVerdict _ _ = False

producedAccepted : Production -> Bool
producedAccepted (ClosureProduced _ GraphAccepted) = True
producedAccepted _ = False

producedRejected : Production -> Bool
producedRejected (ClosureProduced _ (GraphRejected _)) = True
producedRejected _ = False

producerInconclusive : Production -> Bool
producerInconclusive (ProductionInconclusive _) = True
producerInconclusive _ = False

producerInvalid : Production -> Bool
producerInvalid (ProductionInvalid _) = True
producerInvalid _ = False

verifiedProduction : List Nat -> List Call -> Bool
verifiedProduction arities direct = case produce arities direct of
  ClosureProduced certificate verdict => sameVerdict verdict (verify arities direct certificate)
  _ => False

public export
checks : List (String, Bool)
checks =
  [ ("size-change relation algebra exhausts all three relations", algebra)
  , ("empty and acyclic supplied graphs need no cycle witness",
      accepted (verify [] [] []) && accepted (verify [1, 1] [Edge 0 1 [[Unknown]]] [Edge 0 1 [[Unknown]]]))
  , ("strict self-call has a valid closed certificate", accepted (verify [1] [strict] [strict]))
  , ("one-argument self-loop criterion exhausts relations",
      all (\relation =>
        let edge = Edge 0 0 [[relation]] in
          accepted (verify [1] [edge] [edge]) == (relation == Decreases)) relations)
  , ("rectangular composition respects caller and callee orientation",
      let first = Edge 0 1 [[Decreases, NonIncreasing]]
          second = Edge 1 2 [[NonIncreasing], [Decreases]]
          composed = Edge 0 2 [[Decreases, NonIncreasing], [Decreases, Decreases]]
          wrong = Edge 0 2 [[NonIncreasing, Decreases], [Decreases, Decreases]] in
      accepted (verify [2, 1, 2] [first, second] [first, second, composed]) &&
      rejected (verify [2, 1, 2] [first, second] [first, second, wrong]))
  , ("composition chooses the strongest intermediate witness",
      let first = Edge 0 1 [[NonIncreasing], [Decreases]]
          second = Edge 1 2 [[NonIncreasing, NonIncreasing]]
          composed = Edge 0 2 [[Decreases]]
          weakResult = Edge 0 2 [[NonIncreasing]] in
      accepted (verify [1, 2, 1] [first, second] [first, second, composed]) &&
      rejected (verify [1, 2, 1] [first, second] [first, second, weakResult]))
  , ("weak or unknown idempotent self-calls fail the graph criterion",
      rejected (verify [1] [weak] [weak]) && rejected (verify [1] [unknown] [unknown]))
  , ("distinct alternative calls cannot be merged into a strict edge",
      rejected (verify [1] [weak, strict] [weak, strict]) &&
      rejected (verify [1] [weak, strict] [strict]) &&
      rejected (verify [1] [weak] [strict]))
  , ("alternating descent requires the complete composed closure",
      accepted (verify [2] [swapDescending] [swapDescending, strictDiagonal2, strictSwap]) &&
      rejected (verify [2] [swapDescending] [swapDescending]))
  , ("alternating non-strict relations do not establish descent",
      rejected (verify [2] [weakSwap] [weakSwap, weakDiagonal2]))
  , ("mutual calls use both directions and all intermediate compositions",
      let forward = Edge 0 1 [[Decreases]]
          back = Edge 1 0 [[NonIncreasing]]
          backStrict = Edge 1 0 [[Decreases]]
          first = Edge 0 0 [[Decreases]]
          second = Edge 1 1 [[Decreases]] in
      accepted (verify [1, 1] [forward, back] [forward, back, backStrict, first, second]) &&
      rejected (verify [1, 1] [forward, back] [forward, back]))
  , ("certificate cannot omit a direct call or contain duplicates",
      rejected (verify [1] [strict] []) && rejected (verify [1] [strict] [strict, strict]))
  , ("malformed endpoints and dimensions fail closed",
      rejected (verify [1] [Edge 0 1 [[Decreases]]] []) &&
      rejected (verify [1] [Edge 0 0 []] []) &&
      rejected (verify [1] [Edge 0 0 [[Decreases, Unknown]]] []) &&
      rejected (verify [1] [] [Edge 0 0 (replicate 9 [Unknown])]))
  , ("zero-argument cycles cannot have a strict diagonal",
      accepted (verify [0] [] []) && rejected (verify [0] [Edge 0 0 []] [Edge 0 0 []]))
  , ("documented admission maxima are admitted",
      let edges : List Call = concatMap (\caller => map (\callee => Edge caller callee []) [4, 5, 6, 7, 8, 9, 10, 11]) [0, 1, 2, 3] in
      accepted (verify (replicate 16 0) [] []) &&
      accepted (verify [8] [] []) &&
      accepted (verify [1] (replicate 128 strict) [strict]) &&
      accepted (verify (replicate 12 0) edges edges))
  , ("finite graph and certificate caps report inconclusive",
      inconclusive (verify (replicate 17 0) [] []) &&
      inconclusive (verify [9] [] []) &&
      inconclusive (verify [1] (replicate 129 strict) []) &&
      inconclusive (verify [1] [] (replicate 33 strict)))
  , ("producer accepts an empty graph after a stable round",
      case produceWithFuel 1 [] [] of
        ClosureProduced [] GraphAccepted => True
        _ => False)
  , ("producer deduplicates direct calls in deterministic order",
      case produce [1] [strict, strict] of
        ClosureProduced [edge] GraphAccepted => edge == strict
        _ => False)
  , ("producer carries the verifier's rejected cycle verdict",
      producedRejected (produce [1] [weak]) && producedRejected (produce [1] [unknown]) &&
      producedRejected (produce [0] [Edge 0 0 []]))
  , ("producer retains distinct alternative call matrices",
      case produce [1] [strict, weak] of
        ClosureProduced [first, second] (GraphRejected _) => first == strict && second == weak
        _ => False)
  , ("producer saturates alternating descent in three snapshot rounds",
      producerInconclusive (produceWithFuel 2 [2] [swapDescending]) &&
      producedAccepted (produceWithFuel 3 [2] [swapDescending]) &&
      case produce [2] [swapDescending] of
        ClosureProduced [first, second, third] GraphAccepted =>
          first == swapDescending && second == strictDiagonal2 && third == strictSwap
        _ => False)
  , ("producer composes mutual calls in both operand positions",
      let forward = Edge 0 1 [[Decreases]]
          back = Edge 1 0 [[NonIncreasing]]
          backStrict = Edge 1 0 [[Decreases]] in
      case produce [1, 1] [forward, back] of
        ClosureProduced certificate GraphAccepted =>
          elem backStrict certificate && elem (Edge 0 0 [[Decreases]]) certificate &&
          elem (Edge 1 1 [[Decreases]]) certificate && verifiedProduction [1, 1] [forward, back]
        _ => False)
  , ("producer handles rectangular composition and stronger witnesses",
      let first = Edge 0 1 [[NonIncreasing], [Decreases]]
          second = Edge 1 2 [[NonIncreasing, NonIncreasing]] in
      case produce [1, 2, 1] [first, second] of
        ClosureProduced certificate GraphAccepted => elem (Edge 0 2 [[Decreases]]) certificate
        _ => False)
  , ("every completed small one-argument graph has the verifier's verdict",
      all (\a => all (\b => verifiedProduction [1] [Edge 0 0 [[a]], Edge 0 0 [[b]]]) relations) relations)
  , ("producer admission and fuel fail closed",
      producerInvalid (produce [1] [Edge 0 1 [[Decreases]]]) &&
      producerInvalid (produce [1] [Edge 0 0 [[Unknown, Unknown]]]) &&
      producerInconclusive (produce (replicate 17 0) []) &&
      producerInconclusive (produce [9] []) &&
      producerInconclusive (produce [1] (replicate 129 strict)) &&
      producerInconclusive (produceWithFuel 0 [1] [strict]) &&
      producerInconclusive (produceWithFuel 34 [] []) &&
      producedAccepted (produceWithFuel 1 [1] [strict]))
  , ("producer accepts a full closed certificate but not a required 33rd edge",
      let acyclic : List Call = concatMap (\caller => map (\callee => Edge caller callee []) [4, 5, 6, 7, 8, 9, 10, 11]) [0, 1, 2, 3]
          fillers : List Call = take 30 (concatMap (\caller => map (\callee => Edge caller callee []) [7, 8, 9, 10, 11, 12, 13, 14]) [3, 4, 5, 6])
          needsExtra = Edge 0 1 [] :: Edge 1 2 [] :: fillers in
      producedAccepted (produce (replicate 12 0) acyclic) &&
      producerInconclusive (produce (replicate 15 0) needsExtra) &&
      producerInconclusive (produce (replicate 13 0)
        (take 33 (concatMap (\caller => map (\callee => Edge caller callee []) [4, 5, 6, 7, 8, 9, 10, 11, 12]) [0, 1, 2, 3]))))
  ]
