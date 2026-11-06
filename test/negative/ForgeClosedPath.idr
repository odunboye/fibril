-- This module must not type-check: checked path witnesses are opaque.
module ForgeClosedPath

import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.ClosedCorePath
import Fibril.Foundation.DeMorgan.IndependentPath

forged : CheckedClosedPath
forged = MkCheckedClosedPath (CoreAbstract (CoreTerm BoolTrue)) BoolTrue BoolTrue
