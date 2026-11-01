module Tests.UTF8

import Fibril.Source.UTF8
import Data.String

%default total

decodes : List Bits8 -> String -> Bool
decodes bytes expected =
  case decodeUTF8 bytes of
    Right actual => actual == expected
    Left _ => False

rejects : List Bits8 -> Nat -> Bool
rejects bytes offset =
  case decodeUTF8 bytes of
    Left err => err.byteOffset == offset
    Right _ => False

||| RFC boundary and malformed-sequence regressions, independent of host decoding.
public export
checks : List (String, Bool)
checks =
  [ ("UTF8 empty", decodes [] "")
  , ("UTF8 ASCII", decodes [65, 0, 127] (pack ['A', chr 0, chr 127]))
  , ("UTF8 two byte minimum", decodes [0xC2, 0x80] (singleton (chr 0x80)))
  , ("UTF8 two byte maximum", decodes [0xDF, 0xBF] (singleton (chr 0x7FF)))
  , ("UTF8 three byte minimum", decodes [0xE0, 0xA0, 0x80] (singleton (chr 0x800)))
  , ("UTF8 before surrogate", decodes [0xED, 0x9F, 0xBF] (singleton (chr 0xD7FF)))
  , ("UTF8 after surrogate", decodes [0xEE, 0x80, 0x80] (singleton (chr 0xE000)))
  , ("UTF8 BMP maximum", decodes [0xEF, 0xBF, 0xBF] (singleton (chr 0xFFFF)))
  , ("UTF8 astral minimum", decodes [0xF0, 0x90, 0x80, 0x80] (singleton (chr 0x10000)))
  , ("UTF8 scalar maximum", decodes [0xF4, 0x8F, 0xBF, 0xBF] (singleton (chr 0x10FFFF)))
  , ("UTF8 wave emoji", decodes [0xF0, 0x9F, 0x8C, 0x8A] "🌊")
  , ("UTF8 replacement scalar is valid", decodes [0xEF, 0xBF, 0xBD] (singleton (chr 0xFFFD)))
  , ("UTF8 stray continuation", rejects [0x80] 0)
  , ("UTF8 forbidden overlong lead", rejects [0xC0, 0xAF] 0)
  , ("UTF8 three byte overlong", rejects [0xE0, 0x80, 0xAF] 0)
  , ("UTF8 four byte overlong", rejects [0xF0, 0x80, 0x80, 0xAF] 0)
  , ("UTF8 surrogate rejected", rejects [0xED, 0xA0, 0x80] 0)
  , ("UTF8 above range rejected", rejects [0xF4, 0x90, 0x80, 0x80] 0)
  , ("UTF8 invalid lead", rejects [0xF5, 0x80, 0x80, 0x80] 0)
  , ("UTF8 obsolete five byte lead", rejects [0xF8, 0x88, 0x80, 0x80, 0x80] 0)
  , ("UTF8 truncated two byte", rejects [0xC2] 0)
  , ("UTF8 truncated three byte", rejects [0xE2, 0x82] 0)
  , ("UTF8 truncated four byte", rejects [0xF0, 0x90, 0x80] 0)
  , ("UTF8 continuation location", rejects [65, 0xE2, 0x82, 65] 3)
  , ("UTF8 malformed after astral byte offset",
      rejects [0xF0, 0x9F, 0x8C, 0x8A, 0xFF] 4)
  ]
