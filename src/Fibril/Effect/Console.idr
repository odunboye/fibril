-- Pure action data for the restricted console-entry profile, not core IO typing.
module Fibril.Effect.Console

%default total

||| Effect requests cannot be used as terms, proofs, or normalizer results.
public export
data ConsoleAction = PrintLine String
