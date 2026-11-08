module CommonEndpointAdmissionWrongAdmissibility

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission

bad : (ds : AdmittedDeclarations [] (ADCons LBool (ABool True) (ABool False) ADNil)) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])) ->
  DependentPathAdmissible (checkedDeclarations ds) ps -> CanonicalPathAdmissible ds ps
bad ds ps adm = adm
