-- Prepared host-write requests, separate from pure core IO descriptions.
module Fibril.Effect.Console

%default total

||| Effect requests cannot be used as terms, proofs, or normalizer results.
public export
data ConsoleAction = PrintLine String
