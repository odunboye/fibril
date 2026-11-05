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
  ]
