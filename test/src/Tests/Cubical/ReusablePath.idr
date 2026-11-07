module Tests.Cubical.ReusablePath

import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.ReusablePath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

tele : Telescope 2 1
tele = Extend Empty (Tvar FZ) (Tvar (FS FZ))

public export
checks : List (String, Bool)
checks =
  [ ("reusable path open dependent endpoint and beta", 
      case checkPath {n=1} 12 tele (Tapp FZ (Meet (Var FZ) (Var (FS FZ))))
             (Tvar FZ) (Tapp FZ (Var FZ)) of
        Right p => case applyPath 12 p (Reverse (Var FZ)) of
          Right (Tapp FZ (Meet (Reverse (Var FZ)) (Var FZ))) => True
          _ => False
        _ => False)
  , ("reusable path dual endpoints and face computation",
      case checkPath {n=1} 12 tele (Tapp FZ (Reverse (Var FZ)))
             (Tvar (FS FZ)) (Tvar FZ) of
        Right p => case applyPath 12 p (Var FZ) of
          Right t => case (convertRestricted 12 (Under (SEndpoint FZ False)) tele t (Tvar (FS FZ)),
                           convertRestricted 12 (Under (SEndpoint FZ True)) tele t (Tvar FZ)) of
            (Accepted, Accepted) => True
            _ => False
          _ => False
        _ => False)
  , ("reusable path rejects wrong endpoints",
      case checkPath {n=0} 12 tele (Tapp FZ (Var FZ)) (Tvar (FS FZ)) (Tvar FZ) of
        Left Rejected => True
        _ => False)
  , ("reusable path source and application fuel bounds",
      case (checkPath {n=0} 0 tele (Tapp FZ (Var FZ)) (Tvar FZ) (Tvar (FS FZ)),
            checkPath {n=0} 12 tele (Tapp FZ (Var FZ)) (Tvar FZ) (Tvar (FS FZ))) of
        (Left Exhausted, Right p) => case applyPath 0 p Zero of
          Left Exhausted => True
          _ => False
        _ => False)
  , ("reusable path rejects source dimension outside bound",
      case checkPath {n=12} 100 tele (Tvar FZ) (Tvar FZ) (Tvar FZ) of
        Left Exhausted => True
        _ => False)
  , ("reusable path oversized interval fails closed",
      case checkPath {n=1} 12 tele (Tapp FZ (Meet (Var FZ) (Var FZ)))
             (Tvar FZ) (Tvar (FS FZ)) of
        Right p => case applyPath 12 p (Meet (Meet (Var FZ) (Var FZ)) (Meet (Var FZ) (Var FZ))) of
          Left Exhausted => True
          _ => False
        _ => False)
  , ("reusable path can use an older declared path",
      let ctx : Telescope 2 2 = Extend tele (Tvar FZ) (Tvar FZ) in
      case checkPath {n=0} 12 ctx (Tapp (FS FZ) (Var FZ)) (Tvar FZ) (Tvar (FS FZ)) of
        Right _ => True
        _ => False)
  , ("reusable path can be checked over a second dimension",
      case checkPath {n=1} 12 tele (Tapp FZ (Var (FS FZ))) (Tapp FZ (Var FZ)) (Tapp FZ (Var FZ)) of
        Right p => case applyPath 12 p One of
          Right (Tapp FZ (Var FZ)) => True
          _ => False
        _ => False)
  ]
