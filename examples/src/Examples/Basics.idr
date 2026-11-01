module Examples.Basics

%default total

||| A linear input is returned exactly once.
public export
linearIdentity : (1 value : a) -> a
linearIdentity value = value

public export
greeting : String
greeting = "Hello, Fibril!"
