-- Bounded point diagnostics in scalar coordinates; not terminal-width or LSP mapping.
module Fibril.Source.Diagnostic

import Data.List
import Fibril.Source.Text

%default total

||| A single source point, without pretending core errors have source provenance.
public export
record Diagnostic where
  constructor AtPoint
  position : Position
  message : String

-- Escape rejected/control scalars rather than allowing terminal instructions.
-- Valid non-ASCII text is preserved; its terminal cell width is not inferred.
safeChar : Char -> String
safeChar '\t' = " "
safeChar char =
  if ord char < 0x20 || (ord char >= 0x7F && ord char <= 0x9F)
     then "<" ++ show (ord char) ++ ">"
     else case validateText (pack [char]) of
       Left _ => "<" ++ show (ord char) ++ ">"
       Right _ => pack [char]

safeText : List Char -> String
safeText [] = ""
safeText (char :: rest) = safeChar char ++ safeText rest

label : String -> String
label text =
  let chars = unpack text
   in safeText (take 256 chars) ++ if length chars > 256 then "..." else ""

||| File-level errors have no invented scalar location. Labels escape controls
||| and truncate after 256 input scalars each; this is an output bound only.
public export
renderFileError : String -> String -> String
renderFileError path message = label path ++ ": " ++ label message

skipLine : List Char -> List Char
skipLine [] = []
skipLine ('\r' :: '\n' :: rest) = rest
skipLine ('\r' :: rest) = rest
skipLine ('\n' :: rest) = rest
skipLine (_ :: rest) = skipLine rest

lineAt : Nat -> List Char -> List Char
lineAt Z chars = []
lineAt (S Z) chars = takeWhile (\c => c /= '\r' && c /= '\n') chars
lineAt (S (S n)) chars = lineAt (S n) (skipLine chars)

spaces : Nat -> String
spaces count = pack (replicate count ' ')

||| Render at most 80 source scalars around a point, with a scalar-aligned caret.
||| Tabs display as one space. Escapes are included in caret padding; combining
||| marks/wide glyphs may still differ from terminal cell widths. CRLF is one break.
||| Huge columns are clamped to the selected line; output is bounded, not work.
public export
renderDiagnostic : String -> String -> Diagnostic -> String
renderDiagnostic path source diagnostic =
  let position = diagnostic.position
      chars = lineAt position.line (unpack source)
      target = min (position.column `minus` 1) (length chars)
      start = target `minus` 40
      remaining = drop start chars
      visible = take 80 remaining
      leading = if start == 0 then "" else "..."
      trailing = if length remaining > 80 then "..." else ""
      before = safeText (take (target `minus` start) visible)
      digits = show position.line
      header = label path ++ ":" ++ show position ++ ": " ++ label diagnostic.message
   in header ++ "\n  " ++ digits ++ " | " ++ leading ++ safeText visible ++ trailing ++
      "\n  " ++ spaces (length (unpack digits)) ++ " | " ++
      spaces (length (unpack leading) + length (unpack before)) ++ "^"
