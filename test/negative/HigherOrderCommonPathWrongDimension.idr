module HigherOrderCommonPathWrongDimension

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Face

%default total

decls : CommonDeclarations [] [LBool]
decls = CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths

abstraction : CommonShadowPath {ctx = []} {paths = [LBool]} HigherOrderCommonPathWrongDimension.decls
  (the (ScopedFace 1) STop) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
abstraction = CommonAbstract (CPAtType LHere) (CPAtType LHere)
  (CPAt FZ (Var (FS FZ))) (CPAtType LHere)
  (CommonRefl (CPAtType LHere)) (CommonRefl (CPAtType LHere))

bodyWitness : HigherOrderPathWitness [] [LBool] LBool 2 (CPAt FZ (Var (FS FZ)))
bodyWitness = MkHigherOrderPathWitness (CPAtType LHere) (HOPAt [] [LBool] LBool 2 LHere (Var (FS FZ)))

endpointWitness : HigherOrderPathWitness [] [LBool] LBool 1 (CPAt FZ (Var FZ))
endpointWitness = MkHigherOrderPathWitness (CPAtType LHere) (HOPAt [] [LBool] LBool 1 LHere (Var FZ))

bad : (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])) ->
  (adm : DependentPathAdmissible HigherOrderCommonPathWrongDimension.decls ps) ->
  HigherOrderCommonShadowPath HigherOrderCommonPathWrongDimension.abstraction ps adm
bad ps adm = HOCommonAbstract (MkHigherOrderPathWitness (CPAtType LHere) (HOPAt [] [LBool] LBool 2 LHere (Var FZ))) HigherOrderCommonPathWrongDimension.endpointWitness HigherOrderCommonPathWrongDimension.endpointWitness
  (DepEndpointStructural (DepFaceRefl (AlignPathAt [] [LBool] LBool 2 LHere (Var (FS FZ)))))
  (DepEndpointStructural (DepFaceRefl (AlignPathAt [] [LBool] LBool 2 LHere (Var (FS FZ)))))
