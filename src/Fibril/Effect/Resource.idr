-- Host scope outcomes preserve both operation and cleanup errors.
module Fibril.Effect.Resource

%default total

public export
data ResourceOutcome error value
  = AcquisitionFailed error
  | ResourceFinished (Either error value) (Either error ())
