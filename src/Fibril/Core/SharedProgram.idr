-- Whole reachable-graph admission for checked shared globals.
module Fibril.Core.SharedProgram

import Data.List
import Control.Monad.Identity
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Size
import Fibril.Core.GlobalTraversal
import Fibril.Elaboration.Expression.Payload

%default total

public export
GlobalDeclaration : Type
GlobalDeclaration = (Nat, Quantity, Term 0, Term 0)

-- Each new declaration enqueues its signature/body references once. Duplicate
-- references still spend work. Fuel includes all stored syntax and entry syntax;
-- it is a traversal bound, not a wall-time or heap bound.
collect : GlobalContext -> Nat -> List Nat -> List Nat -> List GlobalDeclaration ->
          Either String (List GlobalDeclaration)
collect globals fuel [] seen found = Right (reverse found)
collect globals Z (_ :: _) seen found = Left "Shared global traversal budget exhausted"
collect globals (S fuel) (key :: pending) seen found =
  if elem key seen then collect globals fuel pending seen found else
    case globalEntry globals key of
      Nothing => Left ("Unknown shared global " ++ show key)
      Just (q, ty, body) => collect globals fuel
        (globalReferences ty ++ globalReferences body ++ pending)
        (key :: seen) ((key, q, ty, body) :: found)

||| Includes dependencies found only in types, erased arguments and dead branches.
||| This must precede capability/backend admission; inspecting a key is insufficient.
public export
reachableErasedGlobals : GlobalContext -> Term n -> Either String (List GlobalDeclaration)
reachableErasedGlobals globals term =
  collect globals (S (coreNodes term + globalSyntaxNodes globals))
    (globalReferences term) [] []

public export
reachableGlobals : RuntimeGlobals -> Term n -> Either String (List GlobalDeclaration)
reachableGlobals globals = reachableErasedGlobals (erasedGlobals globals)

||| Count every reachable signature/body once plus the complete entry syntax.
||| This is an explicit shared-graph policy, distinct from the old expanded-tree policy.
public export
sharedProgramNodes : Term n -> List GlobalDeclaration -> Nat
sharedProgramNodes term declarations = coreNodes term +
  foldr (\(_, _, ty, body), rest => coreNodes ty + coreNodes body + rest) 0 declarations

public export
sharedProgramPayload : Term n -> List GlobalDeclaration -> Nat
sharedProgramPayload term declarations = payloadSize term +
  foldr (\(_, _, ty, body), rest => payloadSize ty + payloadSize body + rest) 0 declarations

||| Replace references only for a whole-graph syntax scan after collecting their
||| definitions. Never use this masked syntax for typing, conversion or execution.
public export
maskGlobalRefs : Term n -> Term n
maskGlobalRefs term = runIdentity (traverseGlobalRefs (\_ => Id UnitValue) term)

||| Occurrence checks must inspect referenced declarations, including erased types.
public export
mentionsNominalGlobals : GlobalContext -> String -> Term n -> Either String Bool
mentionsNominalGlobals globals key term = do
  declarations <- reachableErasedGlobals globals term
  Right (mentionsNominal key (maskGlobalRefs term) ||
    any (\(_, _, ty, body) => mentionsNominal key (maskGlobalRefs ty) ||
      mentionsNominal key (maskGlobalRefs body)) declarations)
