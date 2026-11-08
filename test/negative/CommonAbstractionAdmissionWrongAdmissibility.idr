module CommonAbstractionAdmissionWrongAdmissibility
import CommonAbstractionAdmissionFixture
bad : (input : Result STop) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])) ->
  DependentPathAdmissible (checkedDeclarations (abstractionDeclarations input)) ps ->
  CanonicalPathAdmissible (abstractionDeclarations input) ps
bad input ps adm = adm
