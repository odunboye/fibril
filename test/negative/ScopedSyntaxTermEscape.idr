module ScopedSyntaxTermEscape

import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax

bad : Expr 0 0
bad = Variable FZ
