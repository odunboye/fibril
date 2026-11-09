-- JavaScript supports output-only IO and pure data, excluding regions.
module Fibril.Driver.JavaScript.Admission

import Fibril.Core.Term
import Fibril.Core.OutputAdmission

%default total

public export
supported : Term n -> Bool
supported = outputOnly False
