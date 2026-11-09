module Tests.JavaScript

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Driver.JavaScript.Admission
import Fibril.Driver.JavaScript.Emit

%default total

isRight : Either a b -> Bool
isRight (Right _) = True
isRight _ = False

accepts : Term 0 -> Bool
accepts = supported

public export
checks : List (String, Bool)
checks =
  [ ("JavaScript admits checked output-only IO", isRight (emitCheckedJS (WriteLine (StringValue "hello"))))
  , ("JavaScript independently rejects invalid argument typing", not (isRight (emitCheckedJS
       (Apply (Lambda Unrestricted StringType (WriteLine (Variable FZ))) UnitValue))))
  , ("JavaScript independently rejects discarded linear input", not (isRight (emitCheckedJS
       (Apply (Lambda Linear StringType (IOPure UnitValue)) (StringValue "unused")))))
  , ("JavaScript rejects unknown shared references", not (isRight (emitCheckedJS (GlobalRef 999))))
  , ("JavaScript scans dead branches", not (accepts (BoolCase BoolTrue UnitValue ReadLine)))
  , ("JavaScript scans erased arguments", not (accepts (Apply (Lambda Erased UnitType UnitValue) ReadLine)))
  , ("JavaScript scans empty variant annotations", not (accepts (VariantValue ReadLine 0 Nothing)))
  , ("JavaScript scans variant payloads", not (accepts (VariantValue (VariantType [Just (Unrestricted, UnitType)]) 0 (Just ReadLine))))
  , ("JavaScript scans variant arm types", not (accepts (VariantType [Just (Erased, ReadLine)])))
  , ("JavaScript refuses regions even in erased annotations", not (accepts (Pi Erased (WithRegion UnitType UnitValue) UnitType)))
  ]
