-- Abstract region-indexed handle types only; no creation or file operations.
module Fibril.Source.Primitive.Resource

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global

%default total

public export
resourcePrimitiveGlobals : List GlobalDefinition
resourcePrimitiveGlobals =
  [ GlobalWithQuantity Erased "FileHandle"
      (Pi Erased (Universe 0) (Universe 0))
      (Lambda Erased (Universe 0) (FileHandleType (Variable FZ)))
  ]
