module CommonAbstractionAdmissionWrongFace
import CommonAbstractionAdmissionFixture
bad : Result STop -> Result SBottom
bad input = input
