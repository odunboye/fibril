-- Sequential live-reference table for trusted hosted resource execution.
module Fibril.Runtime.InputOwnership

import Data.IORef
import Fibril.Runtime.ScopedInput

%default total

public export
data InputOwnershipError = UnknownInputReference | StaleInputReference | RevokedInputReference

public export
Eq InputOwnershipError where
  UnknownInputReference == UnknownInputReference = True
  StaleInputReference == StaleInputReference = True
  RevokedInputReference == RevokedInputReference = True
  _ == _ = False

public export
Show InputOwnershipError where
  show UnknownInputReference = "Unknown input reference"
  show StaleInputReference = "Stale input reference"
  show RevokedInputReference = "Revoked input reference"

record Entry where
  constructor Owned
  identity : Nat
  generation : Nat
  lease : Maybe ScopedInput

export
data InputOwnershipTable = Table (IORef (Nat, List Entry))

export
newInputOwnershipTable : IO InputOwnershipTable
newInputOwnershipTable = Table <$> newIORef (0, [])

export
registerInputOwnership : InputOwnershipTable -> ScopedInput -> IO Nat
registerInputOwnership (Table state) lease = do
  (next, entries) <- readIORef state
  writeIORef state (S next, Owned next 0 (Just lease) :: entries)
  pure next

export
inputRegionsCreated : InputOwnershipTable -> IO Nat
inputRegionsCreated (Table state) = fst <$> readIORef state

findEntry : Nat -> List Entry -> Maybe Entry
findEntry identity [] = Nothing
findEntry identity (entry :: rest) =
  if identity == entry.identity then Just entry else findEntry identity rest

replaceEntry : Entry -> List Entry -> List Entry
replaceEntry replacement [] = []
replaceEntry replacement (entry :: rest) =
  if entry.identity == replacement.identity then replacement :: rest
  else entry :: replaceEntry replacement rest

checkEntry : Nat -> Maybe Entry -> Either InputOwnershipError ScopedInput
checkEntry generation Nothing = Left UnknownInputReference
checkEntry generation (Just entry) = case entry.lease of
  Nothing => Left RevokedInputReference
  Just lease => if generation == entry.generation then Right lease else Left StaleInputReference

export
checkInputOwnership : InputOwnershipTable -> Nat -> Nat -> IO (Either InputOwnershipError ())
checkInputOwnership (Table state) identity generation = do
  (_, entries) <- readIORef state
  pure (() <$ checkEntry generation (findEntry identity entries))

||| Revoke independently of generation when a scope exits abnormally. Physical
||| close belongs to the scope/session owner; this table never closes raw files.
export
revokeInputOwnership : InputOwnershipTable -> Nat -> IO ()
revokeInputOwnership (Table state) identity = do
  (next, entries) <- readIORef state
  case findEntry identity entries of
    Nothing => pure ()
    Just entry => writeIORef state (next, replaceEntry (Owned identity entry.generation Nothing) entries)

||| Consume the current generation before reading. EOF and represented read
||| errors still return successor ownership. A stale reference performs no read.
||| This table is sequential, not thread-safe, and relies on session cleanup.
export
covering
readOwnedInput : Nat -> InputOwnershipTable -> Nat -> Nat ->
                 IO (Either InputOwnershipError (Nat, Either ScopedInputError (Maybe String)))
readOwnedInput limit table@(Table state) identity generation = do
  (next, entries) <- readIORef state
  case checkEntry generation (findEntry identity entries) of
    Left err => pure (Left err)
    Right lease => do
      let successor = S generation
      writeIORef state (next, replaceEntry (Owned identity successor (Just lease)) entries)
      response <- readScopedInput limit lease
      case response of
        Left FileLeaseClosed => do
          revokeInputOwnership table identity
          pure (Left RevokedInputReference)
        _ => pure (Right (successor, response))
