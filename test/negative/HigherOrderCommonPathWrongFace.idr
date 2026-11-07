module HigherOrderCommonPathWrongFace

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

abstraction : CommonShadowPath {ctx = []} {paths = [LBool]} HigherOrderCommonPathWrongFace.decls
  (the (ScopedFace 1) STop) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
abstraction = CommonAbstract (CPAtType LHere) (CPAtType LHere)
  (CPAt FZ (Var (FS FZ))) (CPAtType LHere)
  (CommonRefl (CPAtType LHere)) (CommonRefl (CPAtType LHere))

bodyWitness : HigherOrderPathWitness [] [LBool] LBool 2 (CPAt FZ (Var (FS FZ)))
bodyWitness = MkHigherOrderPathWitness (CPAtType LHere) (HOPAt [] [LBool] LBool 2 LHere (Var (FS FZ)))

endpointWitness : HigherOrderPathWitness [] [LBool] LBool 1 (CPAt FZ (Var FZ))
endpointWitness = MkHigherOrderPathWitness (CPAtType LHere) (HOPAt [] [LBool] LBool 1 LHere (Var FZ))

wrongFace : (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])) ->
  (adm : DependentPathAdmissible HigherOrderCommonPathWrongFace.decls ps) ->
  DependentEndpointFaceEvidence
    {face = SConjunction (weakenFace (the (ScopedFace 1) (SEndpoint FZ False))) (SEndpoint FZ False)}
    (CommonRefl (CPAtType {i = Var (FS FZ)} LHere))
    (pathWitness HigherOrderCommonPathWrongFace.bodyWitness) (pathWitness HigherOrderCommonPathWrongFace.bodyWitness) ps adm
wrongFace ps adm = (DepEndpointStructural (DepFaceRefl (AlignPathAt [] [LBool] LBool 2 LHere (Var (FS FZ)))))

bad : (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])) ->
  (adm : DependentPathAdmissible HigherOrderCommonPathWrongFace.decls ps) ->
  HigherOrderCommonShadowPath HigherOrderCommonPathWrongFace.abstraction ps adm
bad ps adm = HOCommonAbstract HigherOrderCommonPathWrongFace.bodyWitness HigherOrderCommonPathWrongFace.endpointWitness HigherOrderCommonPathWrongFace.endpointWitness
  (HigherOrderCommonPathWrongFace.wrongFace ps adm)
  (DepEndpointStructural (DepFaceRefl (AlignPathAt [] [LBool] LBool 2 LHere (Var (FS FZ)))))
