module Tests.Declaration

import Data.List
import Fibril.Core.Term
import Fibril.Source.Syntax
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Parser
import Fibril.Source.Declaration
import Fibril.Source.Document
import Fibril.Elaboration.Declaration
import Fibril.Elaboration.Interface
import Fibril.Source.Symbol
import Fibril.Source.Navigation
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

accepted : Bool -> String -> Bool
accepted erased source = case checkSource erased source of
  Right _ => True
  Left _ => False

parseFails : String -> Bool
parseFails source = case resolveSource source of
  Left (Parsing _) => True
  _ => False

resolutionFails : String -> Bool
resolutionFails source = case resolveSource source of
  Left (Resolving _) => True
  _ => False

program : String
program = "not : (1 flag : Bool) -> Bool\nnot = \\(1 flag : Bool) => if flag then False else True\nmain : Bool\nmain = not False\n"

public export
checks : List (String, Bool)
checks =
  [ ("recursive-data generated IR is admitted before construction",
      let source = "module Main\ndata Chain : Type where\n  eliminator foldChain\n  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n" in
      case parseDocument 64 256 source of
        Right document => case document.body of
          DeclarationDocument declarations =>
            case (elaborateDeclarationsInWithBudget (Just "Main") [] 511 10 declarations,
                  elaborateDeclarationsInWithBudget (Just "Main") [] 512 10 declarations) of
              (Left _, Right generated) => length generated == 4
              _ => False
          _ => False
        _ => False)
  , ("sequence-data generated IR is admitted before construction",
      let source = "module Main\ndata Items {0 A : Type} : Type where\n  eliminator foldItems\n  Empty : Items A\n  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n" in
      case parseDocument 64 256 source of
        Right document => case document.body of
          DeclarationDocument declarations =>
            case (elaborateDeclarationsInWithBudget (Just "Main") [] 767 10 declarations,
                  elaborateDeclarationsInWithBudget (Just "Main") [] 768 10 declarations) of
              (Left _, Right generated) => length generated == 4
              _ => False
          _ => False
        _ => False)
  , ("named function equation inherits a dependent signature and quantities",
      accepted False "identity : (0 A : Type) -> (1 item : A) -> A\nidentity T value = value\nmain : Bool\nmain = identity Bool True")
  , ("named function equation rejects linear duplication",
      not (accepted False "duplicate : (1 text : String) -> String\nduplicate text = appendString text text\nmain : String\nmain = duplicate \"x\""))
  , ("references API includes binding and uses in source order",
      case referencesAt "\\(1 x : Bool) => x" 1 18 of
        Right [binding, use] => binding.start.column == 5 && use.start.column == 18
        _ => False)
  , ("references API does not invent unresolved uses",
      case referencesAt "unknown" 1 1 of Right [] => True; _ => False)
  , ("navigation API accepts unsaved source",
      case definitionAt "\\(1 x : Bool) => x" 1 18 of
        Right (Just target) => target.start.column == 5
        _ => False)
  , ("navigation API reports no target for prelude names",
      case definitionAt "putStrLn" 1 1 of
        Right Nothing => True
        _ => False)
  , ("symbols retain signature and definition name spans",
      case documentSymbols "0 item : Bool\nitem = True\n" of
        Right [symbol] => symbol.name == "item" &&
          symbol.range.start.column == 1 && symbol.selection.start.column == 3 &&
          symbol.selection.finish.column == 7 &&
          symbol.definitionSelection.start.line == 2 &&
          symbol.definitionSelection.start.column == 1
        _ => False)
  , ("symbols are syntax only, including unbound names",
      case documentSymbols "helper : Missing\nhelper = unknown\n" of
        Right [symbol] => symbol.name == "helper"
        _ => False)
  , ("symbols accept empty editor buffers",
      case documentSymbols "" of Right [] => True; _ => False)
  , ("symbols accept standalone expressions without declarations",
      case documentSymbols "True" of Right [] => True; _ => False)
  , ("symbols fail atomically on incomplete later declarations",
      case documentSymbols "first : Bool\nfirst = True\nlater : Bool" of
        Left (SymbolParsing _) => True
        _ => False)
  , ("declarations minimal main", accepted False "main : Bool\nmain = True")
  , ("declarations prior function available", accepted False program)
  , ("declarations dependent function signature",
      accepted False
        "id : (0 A : Type 0) -> (1 x : A) -> A\nid = \\(0 A : Type 0) => \\(1 x : A) => x\nmain : Bool\nmain = id Bool True")
  , ("declarations evaluate through typed lets",
      case evaluateSource 4 program of
        Right lines => elem "Normal: True" lines
        Left _ => False)
  , ("declarations let lowering consumes fuel",
      case evaluateSource 3 program of
        Left err => err == "Evaluation budget exhausted; no normal form reported"
        Right _ => False)
  , ("declarations erased checking supports type entry",
      accepted True "main : Type 1\nmain = Type 0")
  , ("declarations runtime rejects type entry",
      not (accepted False "main : Type 1\nmain = Type 0"))
  , ("declarations quantity prefixes preserve linearity",
      accepted False "1 token : Unit\ntoken = ()\n1 main : Unit\nmain = token")
  , ("declarations unrestricted capture cannot duplicate linear binding",
      not (accepted False "1 token : Unit\ntoken = ()\nmain : Unit\nmain = token"))
  , ("declarations linear unused binding rejected",
      not (accepted False "main : Bool\nmain = True\n1 unused : Unit\nunused = ()"))
  , ("declarations erased extraction rejected",
      not (accepted False "0 bit : Bool\nbit = True\nmain : Bool\nmain = bit"))
  , ("declarations no self recursion",
      resolutionFails "main : Bool\nmain = main")
  , ("declarations no forward reference",
      resolutionFails "main : Bool\nmain = other\nother : Bool\nother = True")
  , ("declarations prior values remain opaque during body checking",
      not (accepted False "0 Bit : Type 0\nBit = Bool\nmain : Bit\nmain = True"))
  , ("declarations indented continuations",
      accepted False "main :\n  Bool\nmain =\n  if True\n    then True\n    else False")
  , ("declarations CRLF and comments",
      accepted False "-- comment\r\nmain : Bool\r\nmain =\r\n  True\r\n")
  , ("declarations duplicate name rejected",
      parseFails "main : Bool\nmain = True\nmain : Bool\nmain = False")
  , ("declarations matching definition name required",
      parseFails "main : Bool\nother = True")
  , ("declarations main required", parseFails "other : Bool\nother = True")
  , ("declarations headers must start at column one",
      parseFails " main : Bool\n main = True")
  , ("declarations type and value headers must be separate",
      parseFails "main : Bool main = True")
  , ("declarations missing value rejected",
      parseFails "main : Bool\nmain =")
  , ("declarations no unindented continuation",
      parseFails "main : Bool\nmain =\nTrue")
  , ("declarations count budget explicit",
      let source = "other : Bool\nother = True\nmain : Bool\nmain = other"
       in case lexSource source of
         Left _ => False
         Right tokens =>
           case parseSource 1 256 (advancePosition (At 0 1 1) (unpack source)) tokens of
             Left err => err.message == "Declaration count budget exhausted"
             Right _ => False)
  , ("declarations expression mode unchanged",
      accepted False "(\\(1 x : Bool) => x) True")
  ]
