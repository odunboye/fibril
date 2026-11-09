-- Small JSON rendering boundary; strings are data, never diagnostic syntax.
module Fibril.Driver.JSON

import Fibril.Source.Resolve.Error

import Data.List
import Fibril.Source.Text

%default total

hexDigit : Int -> Char
hexDigit value = chr (if value < 10 then ord '0' + value else ord 'a' + value - 10)

escape : Char -> String
escape '"' = "\\\""
escape '\\' = "\\\\"
escape char = if ord char < 0x20
  then "\\u00" ++ pack [hexDigit (ord char `div` 16), hexDigit (ord char `mod` 16)]
  else pack [char]

public export
jsonString : String -> String
jsonString value = "\"" ++ concat (map escape (unpack value)) ++ "\""

public export
jsonArray : List String -> String
jsonArray values = "[" ++ concat (intersperse "," values) ++ "]"

public export
jsonObject : List (String, String) -> String
jsonObject fields = "{" ++ concat (intersperse ","
  (map (\(key, value) => jsonString key ++ ":" ++ value) fields)) ++ "}"

public export
jsonPosition : Position -> String
jsonPosition at = jsonObject [("offset", show at.offset), ("line", show at.line),
                              ("column", show at.column)]

public export
protocolJSON : List (String, String) -> String
protocolJSON fields = jsonObject
  ([("version", "1"), ("coordinates", jsonString "unicode-scalars;offset=0;line=1;column=1")] ++ fields)

public export
completionFields : Maybe CompletionScope -> List (String, String)
completionFields Nothing = []
completionFields (Just scope) = [("completionScope", jsonObject
  [("query", jsonString scope.query), ("candidates", jsonArray (map candidateJSON scope.candidates))])]
  where
    candidateJSON : CompletionCandidate -> String
    candidateJSON entry = jsonObject
      [("label", jsonString entry.label), ("detail", jsonString entry.detail),
       ("kind", jsonString entry.kind), ("identity", maybe "null" jsonString entry.identity),
       ("compatible", if entry.compatible then "true" else "false")]
