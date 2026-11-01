module Tests.SourceText

import Fibril.Source.Text

%default total

accepted : String -> Bool
accepted source =
  case validateText source of
    Right original => original == source
    Left _ => False

bidiAt : String -> Nat -> Nat -> Nat -> Bool
bidiAt source offset line column =
  case validateText source of
    Left (Rejected at BidiControl _) =>
      at.offset == offset && at.line == line && at.column == column
    _ => False

||| Text boundary tests; no identifier grammar or UTF-8 decoder exists yet.
public export
checks : List (String, Bool)
checks =
  [ ("source ASCII unchanged", accepted "identity x = x")
  , ("source mathematical notation unchanged", accepted "λ x → Π A")
  , ("source non-Latin text unchanged", accepted "日本語 Ελληνικά")
  , ("source emoji unchanged", accepted "hello 🌊")
  , ("source joined emoji unchanged", accepted (pack ['👩', chr 0x200D, '💻']))
  , ("source combining marks preserved", accepted (pack ['e', chr 0x0301]))
  , ("source line endings and tabs preserved", accepted "a\r\n\tb\nc\r")
  , ("source NUL rejected", case validateText (pack ['a', chr 0]) of
      Left (Rejected at ControlCharacter 0) => at.offset == 1 && at.column == 2
      _ => False)
  , ("source BOM rejected", case validateText (pack [chr 0xFEFF, 'a']) of
      Left (Rejected at ByteOrderMark _) => at.offset == 0 && at.line == 1
      _ => False)
  , ("source bidi location after CRLF",
      bidiAt ("x\r\ny" ++ pack [chr 0x202E]) 4 2 2)
  , ("source bidi location after astral scalar",
      bidiAt ("🌊" ++ pack [chr 0x2066]) 1 1 2)
  , ("source bidi location after tab",
      bidiAt ("\t" ++ pack [chr 0x200F]) 1 1 2)
  , ("source Unicode line separator rejected",
      case validateText (pack [chr 0x2028]) of
        Left (Rejected _ ControlCharacter _) => True
        _ => False)
  , ("source raw bidi rejected even between quotes",
      case validateText ("\"" ++ pack [chr 0x202E] ++ "\"") of
        Left (Rejected _ BidiControl _) => True
        _ => False)
  ]
