module BoolCasesWrongOutput

import Fibril.Cubical.Source.BoolCases

bad : BoolAgreement Input (Literal True)
bad = ByBoolCases Refl Refl
