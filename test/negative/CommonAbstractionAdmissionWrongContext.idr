module CommonAbstractionAdmissionWrongContext
import CommonAbstractionAdmissionFixture
bad : AdmittedCanonicalAbstractionInput [LBool] ADNil STop (the (AdmissionPathTerm 1 0 0) (APOrdinary (AVar FZ))) (APOrdinary (AVar FZ)) (APOrdinary (AVar FZ)) LBool ->
  AdmittedCanonicalAbstractionInput [LUnit] ADNil STop (the (AdmissionPathTerm 1 0 0) (APOrdinary (AVar FZ))) (APOrdinary (AVar FZ)) (APOrdinary (AVar FZ)) LBool
bad input = input
