module Examples.Checking

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime

%default total

||| Ask the prototype checker to validate an explicitly represented polymorphic
||| identity. This is erased ordinary checking, not source compilation.
public export
identityChecks : Bool
identityChecks =
  let term = Lambda Erased (Universe 0)
               (Lambda Linear (Variable FZ) (Variable FZ))
      ty = Pi Erased (Universe 0)
             (Pi Linear (Variable FZ) (Variable (FS FZ)))
   in case checkErased 30 30 Empty term ty of
        Right () => True
        Left _ => False

||| Validate the same polymorphic identity with runtime resource accounting.
||| The erased type argument is not counted as a runtime use.
public export
runtimeIdentityChecks : Bool
runtimeIdentityChecks =
  let term = Lambda Erased (Universe 0)
               (Lambda Linear (Variable FZ) (Variable FZ))
      ty = Pi Erased (Universe 0)
             (Pi Linear (Variable FZ) (Variable (FS FZ)))
   in case checkRuntime 40 40 Empty term ty of
        Right _ => True
        Left _ => False
