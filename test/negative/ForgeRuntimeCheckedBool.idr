-- This module must not type-check: runtime endpoint witnesses are opaque.
module ForgeRuntimeCheckedBool

import Fibril.Foundation.DeMorgan.IndependentPath

forged : CheckedClosedBool -> RuntimeCheckedClosedBool
forged = MkRuntimeCheckedClosedBool
