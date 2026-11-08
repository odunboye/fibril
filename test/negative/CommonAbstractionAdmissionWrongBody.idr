module CommonAbstractionAdmissionWrongBody
import CommonAbstractionAdmissionFixture
bad : Result STop -> AdmittedCanonicalAbstractionInput [] CommonAbstractionAdmissionFixture.rawDeclarations STop CommonAbstractionAdmissionFixture.leftRaw CommonAbstractionAdmissionFixture.rightRaw (APAt FZ (Var (FS FZ))) LBool
bad input = input
