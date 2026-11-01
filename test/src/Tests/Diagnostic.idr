module Tests.Diagnostic

import Data.List
import Fibril.Source.Text
import Fibril.Source.Diagnostic
import Fibril.Source.Resolve
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

contains : String -> String -> Bool
contains needle text = isInfixOf (unpack needle) (unpack text)

render : String -> Position -> String
render source position = renderDiagnostic "input.fib" source (AtPoint position "message")

public export
checks : List (String, Bool)
checks =
  [ ("diagnostic line and caret",
      render "abc\nbad" (At 5 2 2) ==
        "input.fib:2:2: message\n  2 | bad\n    |  ^")
  , ("diagnostic CRLF is one break",
      render "abc\r\nbad" (At 5 2 1) ==
        "input.fib:2:1: message\n  2 | bad\n    | ^")
  , ("diagnostic bare CR is one break",
      render "abc\rbad" (At 4 2 1) ==
        "input.fib:2:1: message\n  2 | bad\n    | ^")
  , ("diagnostic tabs shown as logical spaces",
      render "\tbad" (At 1 1 2) ==
        "input.fib:1:2: message\n  1 |  bad\n    |  ^")
  , ("diagnostic EOF after newline",
      render "()\n" (At 3 2 1) ==
        "input.fib:2:1: message\n  2 | \n    | ^")
  , ("diagnostic empty input",
      render "" (At 0 1 1) ==
        "input.fib:1:1: message\n  1 | \n    | ^")
  , ("diagnostic EOF on current line",
      render "x" (At 1 1 2) ==
        "input.fib:1:2: message\n  1 | x\n    |  ^")
  , ("diagnostic large columns do not allocate huge padding",
      let output = render (pack (replicate 200 'x')) (At 10000 1 10001)
       in contains "..." output && length (unpack output) < 256)
  , ("diagnostic early point truncates long right edge",
      let output = render (pack (replicate 200 'x')) (At 0 1 1)
       in contains "..." output && length (unpack output) < 160)
  , ("diagnostic escapes terminal instructions",
      let source = "a" ++ pack [chr 27, chr 0x202E] ++ "b"
          output = render source (At 1 1 2)
       in contains "<27><8238>" output &&
          not (elem (chr 27) (unpack output)) &&
          not (elem (chr 0x202E) (unpack output)))
  , ("diagnostic label controls cannot inject lines",
      renderFileError "a\nb" "message\r" == "a<10>b: message<13>")
  , ("diagnostic long file labels retain coordinates",
      contains "...:1:1: message"
        (renderDiagnostic (pack (replicate 300 'x')) "x" (AtPoint (At 0 1 1) "message")))
  , ("diagnostic Unicode spelling preserved",
      contains "λ" (render "λ" (At 0 1 1)))
  , ("structured checking retains resolution error",
      case checkSourceDetailed False "missing" of
        Left (FrontendFailure (Resolving err)) => err.name == "missing"
        _ => False)
  , ("structured evaluation retains resolution error",
      case evaluateSourceDetailed 10 "missing" of
        Left (FrontendFailure (Resolving err)) => err.name == "missing"
        _ => False)
  , ("diagnostic core failure has no fabricated caret",
      case checkSourceDetailed False "Bool" of
        Left err => let output = renderDriverError "input.fib" "Bool" err
                     in contains "input.fib: Runtime checking:" output &&
                        not (contains "^" output)
        Right _ => False)
  ]
