-- Checked closed non-recursive data construction, not a source parser or certificate.
module Fibril.Elaboration.Data

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Source.Global
import Fibril.Source.Lexer

%default total

||| Untrusted scoped declaration input. Payloads may be arbitrary checked packages;
||| source field-telescope packing and recursive declarations are separate work.
public export
record DataSpec (n : Nat) where
  constructor DataInput
  moduleName : List String
  name : String
  level : Nat
  params : Context n
  alternatives : List (Maybe (Quantity, Term n))
  constructorNames : List String

||| Layout is ordinary data. Consumers must validate constructor references against
||| checked types and actual canonical packing, not trust a tag from this record.
public export
record ConstructorTag where
  constructor Tag
  name : String
  index : Nat
  payloadQuantity : Maybe Quantity

public export
record DataLayout where
  constructor Layout
  name : String
  parameterCount : Nat
  constructors : List ConstructorTag

||| Returned only after every generated definition checks; still no proof object.
||| No definition is installed or effect executed by this pure builder.
public export
record DataBundle where
  constructor Bundle
  typeDefinition : GlobalDefinition
  constructorDefinitions : List GlobalDefinition
  layout : DataLayout
  remainingNodes : Nat

public export
record DataError where
  constructor InvalidData
  message : String

public export
Show DataError where
  show error = error.message

validName : String -> Bool
validName text = text /= "_" && case lexSource text of
  Right [token] => token.kind == Name && token.spelling == text
  _ => False

||| Canonical spelling, independent of filesystem paths. Module admission remains
||| the driver's job; this validates identifier components, not import authority.
public export
dataKey : List String -> String -> Either DataError String
dataKey [] name = Left (InvalidData "Data declarations require a named module")
dataKey components name =
  if all validName (name :: components)
     then Right (concat (intersperse "." (components ++ [name])))
     else Left (InvalidData "Data keys require referenceable identifier components")

contextSize : Context n -> Nat
contextSize Empty = 0
contextSize (Extend rest _ domain) = contextSize rest + 1 + coreNodes domain

contextCount : Context n -> Nat
contextCount Empty = 0
contextCount (Extend rest _ _) = S (contextCount rest)

armSize : List (Maybe (Quantity, Term n)) -> Nat
armSize [] = 0
armSize (Nothing :: rest) = 1 + armSize rest
armSize (Just (_, ty) :: rest) = 1 + coreNodes ty + armSize rest

constructorCost : Nat -> Nat -> Nat -> List (Maybe (Quantity, Term n)) -> Nat
constructorCost context result shape [] = 0
constructorCost context result shape (Nothing :: rest) =
  2 * context + 2 * result + shape + 2 + constructorCost context result shape rest
constructorCost context result shape (Just (_, ty) :: rest) =
  2 * context + 2 * coreNodes ty + 2 * result + shape + 5 + constructorCost context result shape rest

||| Size-only preflight: includes copied contexts, complete global occurrences,
||| indices and shape annotations, without first constructing generated terms.
public export
dataConstructionCost : DataSpec n -> Nat
dataConstructionCost spec =
  let context = contextSize spec.params
      count = contextCount spec.params
      shape = 1 + armSize spec.alternatives
      nominal = 1 + 2 * count + shape
      family = 2 * context + 5 + nominal
      result = 3 + family + 2 * count
   in family + constructorCost context result shape spec.alternatives

parameterArguments : Context n -> List (Term n)
parameterArguments Empty = []
parameterArguments (Extend rest _ _) = map weaken (parameterArguments rest) ++ [Variable FZ]

closeType : Context n -> Term n -> Term 0
closeType Empty body = body
closeType (Extend rest q domain) body = closeType rest (Pi q domain body)

closeValue : Context n -> Term n -> Term 0
closeValue Empty body = body
closeValue (Extend rest q domain) body = closeValue rest (Lambda q domain body)

validateContext : String -> Context n -> Either DataError ()
validateContext key Empty = Right ()
validateContext key (Extend rest q domain) = do
  if q /= Erased then Left (InvalidData "Data parameters must be erased") else Right ()
  if mentionsNominal key domain then Left (InvalidData "Non-recursive data cannot mention its own key in parameter domains") else Right ()
  validateContext key rest

validateArms : String -> List (Maybe (Quantity, Term n)) -> Either DataError ()
validateArms key [] = Right ()
validateArms key (Nothing :: rest) = validateArms key rest
validateArms key (Just (_, ty) :: rest) = do
  if mentionsNominal key ty then Left (InvalidData "Non-recursive data cannot mention its own key in payloads") else Right ()
  validateArms key rest

validateNames : List String -> List String -> List String -> Either DataError ()
validateNames occupied seen [] = Right ()
validateNames occupied seen (name :: rest) = do
  if elem name occupied || elem name seen
     then Left (InvalidData ("Data binding already exists: " ++ name)) else Right ()
  validateNames occupied (name :: seen) rest

constructorBody : Term n -> Term n -> Nat -> Maybe (Quantity, Term n) -> (Term n, Term n)
constructorBody result shape tag Nothing = (result, NominalValue result (VariantValue shape tag Nothing))
constructorBody result shape tag (Just (q, domain)) =
  (Pi q domain (weaken result), Lambda q domain
    (NominalValue (weaken result) (VariantValue (weaken shape) tag (Just (Variable FZ)))))

makeConstructors : Context n -> Term n -> Term n -> Nat -> List String ->
                   List (Maybe (Quantity, Term n)) -> Either DataError (List GlobalDefinition)
makeConstructors context result shape tag [] [] = Right []
makeConstructors context result shape tag (name :: names) (arm :: arms) = do
  let (ty, value) = constructorBody result shape tag arm
  let definition = Global name (closeType context ty) (closeValue context value)
  case checkRuntime checkingDepth typeReductionFuel Empty definition.value definition.declaredType of
    Left error => Left (InvalidData ("Data constructor " ++ name ++ ": " ++ show error))
    Right _ => Right ()
  following <- makeConstructors context result shape (S tag) names arms
  Right (definition :: following)
makeConstructors _ _ _ _ _ _ = Left (InvalidData "Exactly one constructor name is required per alternative")

layoutTags : Nat -> List String -> List (Maybe (Quantity, Term n)) -> List ConstructorTag
layoutTags _ [] _ = []
layoutTags _ _ [] = []
layoutTags tag (name :: names) (arm :: arms) =
  Tag name tag (map fst arm) :: layoutTags (S tag) names arms

||| Allocate qualified identities and independently check a whole closed bundle.
||| occupied uses qualified names; budget is cumulative caller-owned core admission.
||| No metadata is returned on failure, and no recursive/self lookup is installed.
public export
buildData : Nat -> List String -> DataSpec n -> Either DataError DataBundle
buildData budget occupied spec = do
  let estimate = dataConstructionCost spec
  if estimate > budget then Left (InvalidData "Data construction node budget exhausted") else Right ()
  key <- dataKey spec.moduleName spec.name
  if null spec.alternatives then Left (InvalidData "Data requires at least one alternative") else Right ()
  if length spec.alternatives /= length spec.constructorNames
     then Left (InvalidData "Exactly one constructor name is required per alternative") else Right ()
  if not (all validName spec.constructorNames)
     then Left (InvalidData "Constructor names must be referenceable identifiers") else Right ()
  let qualifier = concat (intersperse "." spec.moduleName) ++ "."
  let names = map (qualifier ++) spec.constructorNames
  validateNames occupied [] (key :: names)
  validateContext key spec.params
  validateArms key spec.alternatives
  let shape = VariantType spec.alternatives
  let nominal = NominalType key (parameterArguments spec.params) shape
  -- Ascribe the body before closing binders: universe compatibility is literal,
  -- not propagated through Pi codomains. Preserve the declared family level.
  let body = Apply (Lambda Erased (Universe spec.level) (Variable FZ)) nominal
  let family = GlobalWithQuantity Erased key
                 (closeType spec.params (Universe spec.level)) (closeValue spec.params body)
  case checkErased checkingDepth typeReductionFuel Empty family.value family.declaredType of
    Left error => Left (InvalidData ("Data family " ++ key ++ ": " ++ show error))
    Right () => Right ()
  occurrence <- case lookupGlobal key [family] of
    Nothing => Left (InvalidData "Internal data family occurrence unavailable")
    Just value => Right value
  let result = foldl Apply (rename absurd occurrence) (parameterArguments spec.params)
  definitions <- makeConstructors spec.params result shape 0 names spec.alternatives
  let actual = coreNodes family.declaredType + coreNodes family.value + foldl (\count, definition => count + coreNodes definition.declaredType + coreNodes definition.value) 0 definitions
  if actual /= estimate then Left (InvalidData "Internal data construction estimate was not exact") else Right ()
  Right (Bundle family definitions (Layout key (contextCount spec.params) (layoutTags 0 names spec.alternatives))
           (minus budget actual))
