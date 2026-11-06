-- Compatibility exports; checker defaults have no dependency on the driver.
module Fibril.Driver.Limits

import public Fibril.Core.Limits

%default total

||| Maximum writes admitted by the hosted console planner.
public export
consoleActionLimit : Nat
consoleActionLimit = 64
