module Fibril.Core.Limits

%default total

||| Includes headroom for elaborated continuations and library wrappers.
public export
checkingDepth : Nat
checkingDepth = 512

public export
typeReductionFuel : Nat
typeReductionFuel = 128
