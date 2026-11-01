module Fibril.Driver.Limits

%default total

||| Includes headroom for elaborated do continuations and library wrappers.
public export
checkingDepth : Nat
checkingDepth = 512

public export
typeReductionFuel : Nat
typeReductionFuel = 128
