module Fibril.Source.Resolve.Error

import Fibril.Source.Text

%default total

public export
record CompletionCandidate where
  constructor Candidate
  label : String
  detail : String
  kind : String
  identity : Maybe String
  compatible : Bool

public export
record CompletionScope where
  constructor ScopeAt
  query : String
  candidates : List CompletionCandidate

public export
data ResolveError
  = ResolutionFailure Position String Bool
  | ScopedResolutionFailure Position String Bool CompletionScope

namespace ResolveError
  public export
  position : ResolveError -> Position
  position (ResolutionFailure point _ _) = point
  position (ScopedResolutionFailure point _ _ _) = point

  public export
  name : ResolveError -> String
  name (ResolutionFailure _ text _) = text
  name (ScopedResolutionFailure _ text _ _) = text

  public export
  elaborating : ResolveError -> Bool
  elaborating (ResolutionFailure _ _ value) = value
  elaborating (ScopedResolutionFailure _ _ value _) = value

  public export
  completion : ResolveError -> Maybe CompletionScope
  completion (ResolutionFailure _ _ _) = Nothing
  completion (ScopedResolutionFailure _ _ _ scope) = Just scope

  public export
  (.position) : ResolveError -> Position
  (.position) = position

  public export
  (.name) : ResolveError -> String
  (.name) = name

  public export
  (.elaborating) : ResolveError -> Bool
  (.elaborating) = elaborating

  public export
  (.completion) : ResolveError -> Maybe CompletionScope
  (.completion) = completion

public export
Unbound : Position -> String -> ResolveError
Unbound position name = ResolutionFailure position name False

public export
CannotElaborate : Position -> String -> ResolveError
CannotElaborate position message = ResolutionFailure position message True

public export
Show ResolveError where
  show err = show err.position ++ ": " ++
    (if err.elaborating then err.name else "Unbound name " ++ show err.name)
