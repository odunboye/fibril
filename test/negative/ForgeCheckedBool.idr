-- This module must not type-check: checked Boolean witnesses are opaque.
module ForgeCheckedBool

import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.IndependentPath

forged : CheckedClosedBool
forged = MkCheckedClosedBool BoolTrue
