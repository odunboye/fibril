-- Trusted host orchestration seam; not a source-level ownership certificate.
module Fibril.Runtime.Resource

import Fibril.Effect.Resource

%default total

||| Release exactly once after a represented body result, including failure.
||| Preserve both results. An acquisition failure invokes neither body nor release.
||| Divergence, backend exceptions and process termination are outside this API.
public export
runResourceScope : IO (Either error resource) ->
                   (resource -> IO (Either error value)) ->
                   (resource -> IO (Either error ())) ->
                   IO (ResourceOutcome error value)
runResourceScope acquire body release = do
  acquired <- acquire
  case acquired of
    Left err => pure (AcquisitionFailed err)
    Right resource => do
      result <- body resource
      cleanup <- release resource
      pure (ResourceFinished result cleanup)
