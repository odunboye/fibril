-- This module must not type-check: formed path types are opaque.
module ForgeBoolPathType

import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.IndependentPath

forged : CheckedBoolPathType
forged = MkCheckedBoolPathType BoolTrue BoolFalse
