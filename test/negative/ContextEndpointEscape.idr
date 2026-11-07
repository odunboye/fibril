module ContextEndpointEscape
import Data.Vect

import Data.Fin

import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
bad : PathContext 0 1
bad = [PathBetween FZ FZ]
