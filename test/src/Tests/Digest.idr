module Tests.Digest

import Fibril.Project.Digest

%default total

ascii : String -> List Bits8
ascii s = map (cast . ord) (unpack s)

-- FIPS 180-4 / NIST example vectors.
export
checks : List (String, Bool)
checks =
  [ ("sha256 of the empty input",
      sha256Hex [] == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  , ("sha256 of abc",
      sha256Hex (ascii "abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
  , ("sha256 of a two-block message",
      sha256Hex (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
        == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
  , ("sha256 hashes raw bytes, not text: byte 0xff differs from empty",
      sha256Hex [255] == "a8100ae6aa1940d0b663bb31cd466142ebbdbd5187131b92d93818987832eb89")
  ]
