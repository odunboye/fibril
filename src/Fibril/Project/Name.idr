-- Conservative tool-level name profiles, not source-language module syntax.
module Fibril.Project.Name

%default total

||| A conservative directory slug, not a language/module/package identity rule.
public export
validProjectName : String -> Bool
validProjectName name = case unpack name of
  [] => False
  first :: rest => length (first :: rest) <= 64 && lower first && all allowed rest
  where
    lower : Char -> Bool
    lower c = c >= 'a' && c <= 'z'
    allowed : Char -> Bool
    allowed c = lower c || (c >= '0' && c <= '9') || c == '_' || c == '-'


||| Version-one local inventory identity spelling, intentionally sharing the slug
||| profile. No directory/namespace identity is inferred from this name.
public export
validPackageName : String -> Bool
validPackageName = validProjectName
