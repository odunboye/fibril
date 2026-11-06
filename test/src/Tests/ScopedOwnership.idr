module Tests.ScopedOwnership

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Renaming
import Fibril.Core.Substitution
import Fibril.Core.Substitution.Composition
import Fibril.Driver.Native.Emit
import Fibril.Driver.Interactive
import Fibril.Effect.ConsoleProgram

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 512 128 Empty term ty of
  Right _ => True
  Left _ => False

erased : Term 0 -> Term 0 -> Bool
erased term ty = case checkErased 512 128 Empty term ty of
  Right () => True
  Left _ => False

returnUnit : Term 0
returnUnit = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (IOPure (PairValue
      (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) UnitType)
      (Variable FZ) UnitValue)))

scope : Term 0
scope = WithInputFile UnitType (StringValue "not opened by checking") returnUnit

-- The result may existentially hide a region, but packing the handle there as
-- well as returning it to the scope duplicates ownership and must be rejected.
packageType : Term n
packageType = Sigma Erased Linear (Universe 0) (FileHandleType (Variable FZ))

escapeBody : Term 0
escapeBody = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (IOPure (PairValue
      (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) packageType)
      (Variable FZ)
      (PairValue packageType (Variable (FS FZ)) (Variable FZ)))))

capturedScope : Term 0
capturedScope = Lambda Linear StringType
  (WithInputFile StringType (StringValue "not opened")
    (Lambda Erased (Universe 0)
      (Lambda Linear (FileHandleType (Variable FZ))
        (IOPure (PairValue
          (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) StringType)
          (Variable FZ) (Variable (FS (FS FZ))))))))

nestedScope : Bool -> Term 0
nestedScope useOuter = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (WithInputFile UnitType (StringValue "nested")
      (Lambda Erased (Universe 0)
        (Lambda Linear (FileHandleType (Variable FZ))
          (IOPure (PairValue
            (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) UnitType)
            (if useOuter then Variable (FS (FS FZ)) else Variable FZ) UnitValue))))))

scopeMain : Term 0
scopeMain = IOBind (fileScopeResultType UnitType) UnitType scope
  (Lambda Linear (fileScopeResultType UnitType)
    (VariantCase (Lambda Erased (fileScopeResultType UnitType) (IOType UnitType)) (Variable FZ)
      [Lambda Linear StringType (WriteLine (Variable FZ)),
       Lambda Linear UnitType (UnitCase (Variable FZ) (IOPure UnitValue)),
       Lambda Linear (Sigma Linear Linear UnitType StringType)
         (PairCase (Lambda Erased (Sigma Linear Linear UnitType StringType) (IOType UnitType))
           (Variable FZ)
           (Lambda Linear UnitType (Lambda Linear StringType
             (UnitCase (Variable (FS FZ)) (WriteLine (Variable FZ))))))]))

public export
checks : List (String, Bool)
checks =
  [ ("scope callback returns matching linear ownership",
      accepted returnUnit (scopedInputBodyType UnitType))
  , ("scope checks a region-polymorphic ownership-returning body",
      accepted scope (IOType (fileScopeResultType UnitType)))
  , ("scope request full normalization remains inert",
      case normalize 0 scope of
        Normal result => sameSyntax result scope
        _ => False)
  , ("scope request head normalization remains inert",
      case weakHead 0 scope of
        HeadForm result => sameSyntax result scope
        _ => False)
  , ("scope cannot yield a pure result proof",
      not (erased scope (fileScopeResultType UnitType)))
  , ("scope rejects body without returned ownership",
      not (erased
        (WithInputFile UnitType (StringValue "unused")
          (Lambda Erased (Universe 0)
            (Lambda Linear (FileHandleType (Variable FZ)) (IOPure UnitValue))))
        (IOType (fileScopeResultType UnitType))))
  , ("ownership-returning callback rejects existential handle escape by usage",
      -- The existential package lives in Type1, above this first scope API's
      -- Type0 result limit. Test the callback directly so a universe rejection
      -- cannot masquerade as evidence of linear ownership checking.
      let ty = scopedInputBodyType packageType in
        erased escapeBody ty && not (accepted escapeBody ty))
  , ("scope rejects linear captures skipped by open failure",
      let ty = Pi Linear StringType (IOType (fileScopeResultType StringType)) in
        erased capturedScope ty && not (accepted capturedScope ty))
  , ("nested scope cannot substitute an outer-region handle",
      let ty = Pi Erased (Universe 0)
            (Pi Linear (FileHandleType (Variable FZ)) (IOType (fileScopeResultType UnitType))) in
        erased (nestedScope False) ty && not (erased (nestedScope True) ty))
  , ("scope result can be consumed to form a checked IO Unit entry",
      accepted scopeMain (IOType UnitType))
  , ("output emitter fails closed on inert scoped resources",
      emitCheckedC scopeMain == Left "C backend does not support this computational core construct")
  , ("interactive emitter fails closed on inert scoped resources",
      emitCheckedInteractiveC 64 8192 scopeMain == Left "C backend does not support this computational core construct")
  , ("host interpreter fails closed before scoped resource requests",
      case prepareInteractive 128 128 scopeMain of
        Left _ => False
        Right program => case runScript 0 [] program of
          Scripted (Right (Left InteractiveUnsupported)) [] [] => True
          _ => False)
  , ("scope rejects a non-String path",
      not (erased (WithInputFile UnitType UnitValue returnUnit)
                  (IOType (fileScopeResultType UnitType))))
  , ("scope rejects a higher-universe result type",
      not (erased (WithInputFile (Universe 0) (StringValue "unused") returnUnit)
                  (IOType (fileScopeResultType (Universe 0)))))
  ]
