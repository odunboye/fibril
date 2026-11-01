-- A runnable view of the prototype, not a surface language implementation.
module Fibril.Driver.Demo

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Usage
import Fibril.Core.Pretty
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face

%default total

identity : Term 0
identity = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))

identityType : Term 0
identityType = Pi Erased (Universe 0) (Pi Linear (Variable FZ) (Variable (FS FZ)))

checkDuplication : Either String String
checkDuplication =
  let context = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)
      term = Apply (Lambda Unrestricted (Variable (FS FZ)) (Variable FZ)) (Variable FZ)
   in case inferRuntime 40 40 context term of
        Left (ContextUsage 0 Linear Unrestricted) =>
          Right "Linear duplication: rejected (expected 1, observed unrestricted)"
        Left err => Left ("Unexpected rejection: " ++ show err)
        Right _ => Left "Linear duplication was unexpectedly accepted"

||| Check built-in ordinary terms and cubical algebra examples.
||| Failure is returned to the CLI; no unchecked success banner is emitted.
public export
demoReport : Either String (List String)
demoReport = do
  case checkErased 40 40 Empty identity identityType of
    Left err => Left ("Erased identity: " ++ show err)
    Right () => Right ()
  result <- case checkRuntime 40 40 Empty identity identityType of
    Left err => Left ("Runtime identity: " ++ show err)
    Right result => Right result
  rejected <- checkDuplication
  if equivalent (Reverse (Meet (Var 0) (Var 1)))
                (Join (Reverse (Var 0)) (Reverse (Var 1)))
     then Right ()
     else Left "De Morgan equality check failed"
  if equivalentFace (Conjunction (Endpoint 0 False) (Endpoint 0 True)) Bottom &&
     not (equivalentFace (Disjunction (Endpoint 0 False) (Endpoint 0 True)) Top)
     then Right ()
     else Left "Face boundary check failed"
  Right
    [ "Fibril prototype demo (explicit core; no source parser)"
    , "Identity term: " ++ renderTerm identity
    , "Identity type: " ++ renderTerm result.inferredType
    , "Erased checking: accepted"
    , "Runtime usage checking: accepted; closed usage " ++ show result.usage
    , rejected
    , "De Morgan interval law: passed"
    , "Opposite endpoint faces: disjoint, not exhaustive"
    , "These are prototype checks, not a soundness proof or compiled Fibril program."
    ]
