module CommonAbstractionAdmissionFixture

import public Data.Fin
import public Data.Vect
import public Fibril.Cubical.Logical.Shadow
import public Fibril.Cubical.Logical.ShadowCommon
import public Fibril.Cubical.Logical.CommonAdmission
import public Fibril.Foundation.DeMorgan.Interval
import public Fibril.Foundation.DeMorgan.Scope

public export
leftRaw : AdmissionPathTerm 0 1 1
leftRaw = APOrdinary (ABool True)

public export
rightRaw : AdmissionPathTerm 0 1 1
rightRaw = APOrdinary (ABool False)

public export
bodyRaw : AdmissionPathTerm 0 1 2
bodyRaw = APAt FZ (Var FZ)

public export
rawDeclarations : AdmissionDeclarations 0 1
rawDeclarations = ADCons LBool (ABool True) (ABool False) ADNil

public export
Result : ScopedFace 1 -> Type
Result face = AdmittedCanonicalAbstractionInput [] rawDeclarations face leftRaw rightRaw bodyRaw LBool
