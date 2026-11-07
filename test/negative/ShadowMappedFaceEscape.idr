module ShadowMappedFaceEscape

import Data.Fin
import Data.Vect

import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

decls : PathDeclarations [] [LBool]
decls = DeclarePath (LBoolean True) (LBoolean False) NoPaths

-- The original equality needs i=0; mapping i to itself cannot move it to top.
bad : DimensionEvidence (the (Fin 1 -> ScopedInterval 1) Var) STop
  (BodyEndpoint (DeclaredLeft {face = SEndpoint FZ False} {i = Var FZ} {declarations = ShadowMappedFaceEscape.decls} DeclaredHere Refl))
bad = DimLeft Refl
