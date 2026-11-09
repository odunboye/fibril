module Tests.Embedded

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.OutputAdmission
import Fibril.Driver.Native.Emit

%default total

accepted : Either a b -> Bool
accepted (Right _) = True
accepted _ = False

supports : Term 0 -> Bool
supports = outputOnly True

public export
checks : List (String, Bool)
checks =
  [ ("embedded profile admits checked output-only main", accepted (emitCheckedEmbeddedC (WriteLine (StringValue "hello"))))
  , ("embedded profile independently checks types", not (accepted (emitCheckedEmbeddedC
       (Apply (Lambda Unrestricted StringType (WriteLine (Variable FZ))) UnitValue))))
  , ("embedded profile independently checks linear usage", not (accepted (emitCheckedEmbeddedC
       (Apply (Lambda Linear StringType (IOPure UnitValue)) (StringValue "unused")))))
  , ("embedded profile scans erased input", not (supports (Apply (Lambda Erased UnitType UnitValue) ReadLine)))
  , ("embedded profile scans dead input", not (supports (BoolCase BoolTrue UnitValue ReadLine)))
  , ("embedded profile scans variant annotations", not (supports (VariantValue ReadLine 0 Nothing)))
  , ("embedded profile scans file types", not (supports (Pi Erased (FileHandleType UnitType) UnitType)))
  , ("embedded profile admits region syntax for first-order checking", supports (WithRegion UnitType (Lambda Erased (Universe 0) UnitValue)))
  , ("JavaScript admission still refuses regions", not (outputOnly False (the (Term 0) (WithRegion UnitType UnitValue))))
  , ("embedded profile rejects unknown globals", not (accepted (emitCheckedEmbeddedC (GlobalRef 999))))
  ]
