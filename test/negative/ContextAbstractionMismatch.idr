module ContextAbstractionMismatch

import Data.Fin
import Data.Vect

import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope



bad : CheckedContextAbstraction [PathBetween FZ FZ] (ApplyPath FZ (Var FZ)) FZ FZ ->
      CheckedContextAbstraction [PathBetween FZ (FS FZ)] (ApplyPath FZ (Var FZ)) FZ FZ
bad x = x
