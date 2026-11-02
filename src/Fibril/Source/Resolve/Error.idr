module Fibril.Source.Resolve.Error

import Fibril.Source.Text

%default total

public export
record ResolveError where
  constructor ResolutionFailure
  position : Position
  name : String
  elaborating : Bool

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
