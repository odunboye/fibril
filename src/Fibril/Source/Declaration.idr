-- Grammar and authored declaration framing. Record lowering is a separate pass.
module Fibril.Source.Declaration

import Data.List
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import public Fibril.Source.Declaration.Syntax

%default total

nextPosition : Position -> List Token -> Position
nextPosition end [] = end
nextPosition end (token :: _) = token.span.start

-- The header's remaining tokens and later indented lines form one expression.
-- A later column-one token always starts the next declaration frame.
expressionChunk : Nat -> List Token -> (List Token, List Token)
expressionChunkAt : Nat -> Nat -> List Token -> (List Token, List Token)
expressionChunkAt column headerLine =
  span (\token => token.span.start.line == headerLine || token.span.start.column > column)

expressionChunk headerLine = expressionChunkAt 1 headerLine

equationArguments : Nat -> Position -> Nat -> List String -> List Token -> Either ParseError (List Token, List Token)
equationArguments Z end line seen tokens@(item :: _) =
  if item.kind == Equals then Right ([], tokens)
    else Left (ParseFailure item.span.start "Function equation binder budget exhausted")
equationArguments Z end line seen [] = Left (ParseFailure end "Expected = after function equation")
equationArguments (S budget) end line seen [] = Left (ParseFailure end "Expected = after function equation")
equationArguments (S budget) end line seen tokens@(item :: rest) =
  if item.kind == Equals then Right ([], tokens) else do
    if item.kind /= Name || item.span.start.line /= line
      then Left (ParseFailure item.span.start "Function equation parameters must be names on the definition line") else Right ()
    if item.spelling /= "_" && elem item.spelling seen
      then Left (ParseFailure item.span.start "Duplicate function equation parameter") else Right ()
    (later, remaining) <- equationArguments budget end line (item.spelling :: seen) rest
    Right (item :: later, remaining)

parsePairFramed : Nat -> Nat -> Nat -> Position -> List Token ->
           Either ParseError (Declaration, List Token)
parsePairFramed column definitionColumn expressionBudget end [] = Left (ParseFailure end "Expected declaration signature")
parsePairFramed column definitionColumn expressionBudget end tokens@(first :: _) = do
  if first.span.start.column /= column
     then Left (ParseFailure first.span.start "Declaration headers must start in column 1")
     else Right ()
  (q, afterQuantity) <- binderQuantity tokens
  (name, afterName) <- expect Name end afterQuantity
  (colon, afterColon) <- expect Colon end afterName
  if name.span.start.line /= first.span.start.line ||
     colon.span.start.line /= first.span.start.line
     then Left (ParseFailure name.span.start "Signature name and colon must share the header line")
     else Right ()
  let (typeTokens, afterType) = expressionChunkAt definitionColumn first.span.start.line afterColon
  expected <- parseExpression expressionBudget (nextPosition end afterType) typeTokens
  (definedName, afterDefinedName) <- expect Name end afterType
  if definedName.span.start.column /= definitionColumn
     then Left (ParseFailure definedName.span.start "Definition headers must start in column 1")
     else Right ()
  if definedName.spelling /= name.spelling
     then Left (ParseFailure definedName.span.start
                ("Expected definition of " ++ show name.spelling ++
                 ", found " ++ show definedName.spelling))
     else Right ()
  (arguments, beforeEquals) <- equationArguments expressionBudget end definedName.span.start.line [] afterDefinedName
  (equals, afterEquals) <- expect Equals end beforeEquals
  if equals.span.start.line /= definedName.span.start.line
     then Left (ParseFailure equals.span.start "Definition name and = must share the header line")
     else Right ()
  let (valueTokens, remaining) = expressionChunkAt definitionColumn definedName.span.start.line afterEquals
  body <- parseExpression expressionBudget (nextPosition end remaining) valueTokens
  let value = case arguments of
        [] => body
        first :: _ => NEquationLambda (Between first.span.start (extent body).finish) arguments expected body
  Right (Defined (Between first.span.start (extent body).finish)
                 name.span definedName.span False q name.spelling expected value, remaining)


parsePairAt : Nat -> Nat -> Position -> List Token -> Either ParseError (Declaration, List Token)
parsePairAt column = parsePairFramed column 1

parsePair : Nat -> Position -> List Token -> Either ParseError (Declaration, List Token)
parsePair = parsePairAt 1

directive : TokenKind -> Nat -> Position -> List Token ->
            Either ParseError (Token, Token, List Token)
directive kind indent end tokens = do
  (keyword, rest) <- expect kind end tokens
  (name, remaining) <- expect Name end rest
  if keyword.span.start.column /= indent || indent <= 1 ||
     name.span.start.line /= keyword.span.start.line || name.spelling == "_" ||
     (case remaining of next :: _ => next.span.start.line == keyword.span.start.line; [] => False)
     then Left (ParseFailure keyword.span.start "Record directives need their own aligned indented line and a name")
     else Right (keyword, name, remaining)

parseField : Nat -> Nat -> Position -> List Token -> Either ParseError (RecordField, List Token)
parseField budget indent end [] = Left (ParseFailure end "Expected record field")
parseField budget indent end tokens@(first :: _) = do
  if first.span.start.column /= indent
     then Left (ParseFailure first.span.start "Record fields must align with constructor/eliminator")
     else Right ()
  let (line, remaining) = span (\token => token.span.start.line == first.span.start.line) tokens
  (q, following) <- binderQuantity line
  (name, following) <- expect Name end following
  (_, following) <- expect Colon end following
  ty <- parseExpression budget (nextPosition end remaining) following
  Right (Field name q ty, remaining)

parseFields : Nat -> Nat -> Nat -> Position -> List Token ->
              Either ParseError (List RecordField, List Token)
parseFields fuel budget indent end tokens = case tokens of
  token :: _ => if token.span.start.column <= 1 || token.kind == ProjectionKeyword
    then Right ([], tokens) else case fuel of
      Z => Left (ParseFailure token.span.start "Record field token budget exhausted")
      S fuel => do
        (field, rest) <- parseField budget indent end tokens
        (following, remaining) <- parseFields fuel budget indent end rest
        Right (field :: following, remaining)
  [] => Right ([], [])

parseProjections : Nat -> Nat -> Position -> List Token ->
                   Either ParseError (List RecordProjection, List Token)
parseProjections fuel indent end tokens = case tokens of
  token :: rest => if token.kind /= ProjectionKeyword then Right ([], tokens) else
    case fuel of
      Z => Left (ParseFailure token.span.start "Record projection token budget exhausted")
      S fuel => do
        (name, rest) <- expect Name end rest
        (field, rest) <- expect Name end rest
        if token.span.start.column /= indent || name.spelling == "_" ||
           field.span.start.line /= token.span.start.line ||
           (case rest of next :: _ => next.span.start.line == token.span.start.line; [] => False)
           then Left (ParseFailure token.span.start "Expected aligned projection getter field on its own line")
           else Right ()
        (following, remaining) <- parseProjections fuel indent end rest
        Right (Projected token name field :: following, remaining)
  [] => Right ([], [])

recordParameters : Nat -> Nat -> Position -> List Token ->
                   Either ParseError (List RecordParameter, List Token)
recordParameters fuel expressions end tokens = case tokens of
  token :: _ => if token.kind /= OpenParen then Right ([], tokens) else
    case fuel of
      Z => Left (ParseFailure token.span.start "Record parameter budget exhausted (8)")
      S fuel => do
        parameter <- binder expressions end tokens
        (rest, remaining) <- recordParameters fuel expressions end parameter.remaining
        Right (Parameter parameter.span parameter.quantity parameter.name parameter.domain :: rest, remaining)
  [] => Right ([], [])

optionalEliminator : Nat -> Position -> List Token -> Either ParseError (Maybe (Token, Token), List Token)
optionalEliminator indent end tokens@(next :: _) =
  if next.kind == EliminatorKeyword then do
    (keyword, name, following) <- directive EliminatorKeyword indent end tokens
    Right (Just (keyword, name), following)
  else Right (Nothing, tokens)
optionalEliminator indent end [] = Right (Nothing, [])

dataParameters : Nat -> Nat -> Position -> Maybe Bool -> List Token -> Either ParseError (Bool, List RecordParameter, List Token)
dataParameters Z expressions end mode (token :: _) = Left (ParseFailure token.span.start "Data parameter parsing budget exhausted")
dataParameters fuel expressions end mode [] = Right (fromMaybe False mode, [], [])
dataParameters (S fuel) expressions end mode tokens@(token :: _) =
  if token.kind /= OpenParen && token.kind /= OpenBrace then Right (fromMaybe False mode, [], tokens) else do
    let isImplicit = token.kind == OpenBrace
    case mode of
      Just previous => if previous /= isImplicit then Left (ParseFailure token.span.start "Data parameters must be all explicit or all implicit-constructor binders") else Right ()
      Nothing => Right ()
    parameter <- if isImplicit then implicitDataBinder expressions end tokens else binder expressions end tokens
    (visibility, following, rest) <- dataParameters fuel expressions end (Just isImplicit) parameter.remaining
    Right (visibility, Parameter parameter.span parameter.quantity parameter.name parameter.domain :: following, rest)

dataFields : Nat -> Nat -> Position -> List Token -> Either ParseError (List RecordField, Expr)
dataFields Z expressions end tokens = Left (ParseFailure (nextPosition end tokens) "Constructor telescope parsing budget exhausted")
dataFields (S fuel) expressions end tokens@(opening :: afterOpen) =
  if opening.kind /= OpenParen then do
    result <- parseExpression expressions end tokens
    Right ([], result)
  else do
    (_, names) <- binderQuantity afterOpen
    (name, _) <- expect Name end names
    parameter <- binder expressions end tokens
    (_, following) <- expect Arrow end parameter.remaining
    (fields, result) <- dataFields fuel expressions end following
    Right (Field name parameter.quantity parameter.domain :: fields, result)
dataFields (S fuel) expressions end [] = Left (ParseFailure end "Expected constructor result type")

dataConstructors : Nat -> Nat -> Nat -> Position -> List Token -> Either ParseError (List DataConstructor, List Token)
dataConstructors fuel expressions indent end [] = Right ([], [])
dataConstructors fuel expressions indent end tokens@(first :: _) =
  if first.span.start.column <= 1 then Right ([], tokens) else case fuel of
    Z => Left (ParseFailure first.span.start "Data constructor token budget exhausted")
    S fuel => do
      if first.span.start.column /= indent then Left (ParseFailure first.span.start "Data constructors must align") else Right ()
      let (line, remaining) = span (\token => token.span.start.line == first.span.start.line) tokens
      (name, rest) <- expect Name end line
      (_, rest) <- expect Colon end rest
      (fields, result) <- dataFields (S (length rest)) expressions (nextPosition end remaining) rest
      (following, rest) <- dataConstructors fuel expressions indent end remaining
      Right (DataConstructorSyntax (Between name.span.start (extent result).finish) name fields result :: following, rest)

parseData : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseData budget end tokens = do
  (keyword, rest) <- expect DataKeyword end tokens
  (name, rest) <- expect Name end rest
  (implicitConstructors, params, rest) <- dataParameters (S (length rest)) budget end Nothing rest
  (_, rest) <- expect Colon end rest
  (universe, rest) <- expect TypeKeyword end rest
  (level, _, rest) <- universeAfterType universe rest
  (whereToken, rest) <- expect WhereKeyword end rest
  if keyword.span.start.column /= 1 || name.spelling == "_" || whereToken.span.start.line /= keyword.span.start.line
     then Left (ParseFailure keyword.span.start "Expected column-one data header ending : Type n where on one line") else Right ()
  let indent = case rest of first :: _ => first.span.start.column; [] => 0
  (eliminator, rest) <- optionalEliminator indent end rest
  (constructors, rest) <- dataConstructors (length rest) budget indent end rest
  if null constructors then Left (ParseFailure name.span.start "Data requires at least one constructor") else Right ()
  let finish = case reverse constructors of ctor :: _ => ctor.span.finish; [] => name.span.finish
  Right (DataItem (DataSyntax (Between keyword.span.start finish) name level params implicitConstructors eliminator constructors False), rest)

parseRecordLike : TokenKind -> Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseRecordLike kind budget end tokens = do
  (keyword, rest) <- expect kind end tokens
  (name, rest) <- expect Name end rest
  (params, rest) <- recordParameters 8 budget end rest
  (_, rest) <- expect Colon end rest
  (universe, rest) <- expect TypeKeyword end rest
  (level, _, rest) <- universeAfterType universe rest
  (whereToken, rest) <- expect WhereKeyword end rest
  if keyword.span.start.column /= 1 || name.spelling == "_" ||
     whereToken.span.start.line /= keyword.span.start.line
     then Left (ParseFailure keyword.span.start "Expected a single-line, column-one record header ending : Type n where")
     else Right ()
  let indent = case rest of token :: _ => token.span.start.column; [] => 0
  (constructorKeyword, constructorName, rest) <- directive ConstructorKeyword indent end rest
  if constructorKeyword.span.start.line <= whereToken.span.start.line
     then Left (ParseFailure constructorKeyword.span.start "constructor must follow the record header")
     else Right ()
  (eliminator, rest) <- optionalEliminator indent end rest
  (fields, rest) <- parseFields (length rest) budget indent end rest
  if null fields then Left (ParseFailure constructorName.span.finish "Records require at least one field") else Right ()
  if kind == InterfaceKeyword && (case rest of token :: _ => token.kind == ProjectionKeyword; [] => False)
     then Left (ParseFailure (nextPosition end rest) "Interface methods generate getters; projection directives are not allowed") else Right ()
  (projections, rest) <- parseProjections (length rest) indent end rest
  case rest of
    token :: _ => if token.span.start.column > 1
                    then Left (ParseFailure token.span.start "Records require single-line fields followed by optional projections")
                    else Right ()
    [] => Right ()
  let finish = case reverse projections of
        [] => case reverse fields of
          field :: _ => (extent field.ty).finish
          [] => constructorName.span.finish
        final :: _ => final.field.span.finish
  let region = Between keyword.span.start finish
  let authored = RecordSyntax region name level params constructorKeyword constructorName eliminator fields projections False
  Right (if kind == InterfaceKeyword then InterfaceItem authored else RecordItem authored, rest)

methodBodies : Nat -> Nat -> Nat -> Position -> List Token ->
               Either ParseError (List MethodDefinition, List Token)
methodBodies fuel expressions indent end [] = Right ([], [])
methodBodies fuel expressions indent end tokens@(first :: _) =
  if first.span.start.column <= 1 then Right ([], tokens) else case fuel of
    Z => Left (ParseFailure first.span.start "Implementation method token budget exhausted")
    S fuel => do
      if first.span.start.column /= indent
         then Left (ParseFailure first.span.start "Implementation methods must align") else Right ()
      let (frame, following) = span (\token => token.span.start.line == first.span.start.line || token.span.start.column > indent) tokens
      (name, afterName) <- expect Name end frame
      (equals, valueTokens) <- expect Equals end afterName
      if equals.span.start.line /= name.span.start.line
         then Left (ParseFailure equals.span.start "Method name and = must share their header line") else Right ()
      value <- parseExpression expressions (nextPosition end following) valueTokens
      (rest, remaining) <- methodBodies fuel expressions indent end following
      Right (MethodBody name value :: rest, remaining)

parseImplementationBlock : Nat -> Position -> Token -> List Token -> List Token ->
                           Either ParseError (AuthoredDeclaration, List Token)
parseImplementationBlock budget end keyword header following = do
  (name, rest) <- expect Name end header
  (_, rest) <- expect Colon end rest
  let (typeTokens, whereTokens) = break (\token => token.kind == WhereKeyword) rest
  (_, afterWhere) <- expect WhereKeyword end whereTokens
  if not (null afterWhere)
     then Left (ParseFailure (nextPosition end afterWhere) "where must end the implementation header") else Right ()
  target <- parseExpression budget (nextPosition end following) typeTokens
  let indent = case following of token :: _ => token.span.start.column; [] => 0
  (methods, remaining) <- methodBodies (length following) budget indent end following
  if null methods then Left (ParseFailure name.span.start "Implementation blocks require at least one method") else Right ()
  let finish = case reverse methods of method :: _ => (extent method.value).finish; [] => name.span.finish
  Right (ImplementationBlock (ImplementationSyntax (Between keyword.span.start finish) name target methods False), remaining)

parseImplementation : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseImplementation budget end [] = Left (ParseFailure end "Expected implementation declaration")
parseImplementation budget end (keyword :: rest) = do
  let position = nextPosition end rest
  if keyword.span.start.column /= 1 || position.line /= keyword.span.start.line
     then Left (ParseFailure keyword.span.start "Expected implementation name : DictionaryType on a column-one header") else Right ()
  let (frame, following) = span (\token => token.span.start.line == keyword.span.start.line || token.span.start.column > 1) rest
  let (header, ending) = break (\token => token.kind == WhereKeyword) frame
  case ending of
    marker :: methods => do
      if any (\token => token.span.start.line == marker.span.start.line) methods
         then Left (ParseFailure marker.span.start "where must end the implementation header") else Right ()
      parseImplementationBlock budget end keyword (header ++ [marker]) (methods ++ following)
    [] => do
       (decl, remaining) <- parsePairAt position.column budget end rest
       Right (ImplementationItem ({ dictionary := True, span := Between keyword.span.start decl.span.finish } decl), remaining)


parseMutual : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseMutual budget end (keyword :: marker :: tokens@(first :: _)) = do
  if keyword.span.start.column /= 1 || marker.kind /= WhereKeyword ||
     marker.span.start.line /= keyword.span.start.line || first.span.start.line <= marker.span.start.line ||
     first.span.start.column <= 1
    then Left (ParseFailure keyword.span.start "Expected mutual where followed by two indented declarations") else Right ()
  let indent = first.span.start.column
  (one, rest) <- parsePairFramed indent indent budget end tokens
  (two, remaining) <- parsePairFramed indent indent budget end rest
  case remaining of
    next :: _ => if next.span.start.column > 1
      then Left (ParseFailure next.span.start "Mutual groups require exactly two ordinary declarations") else Right ()
    [] => Right ()
  Right (MutualItem (MutualSyntax (Between keyword.span.start two.span.finish) one two False), remaining)
parseMutual _ end _ = Left (ParseFailure end "Expected mutual where and two declarations")

parseOne : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseOne budget end tokens@(token :: rest) =
  if token.kind == ExportKeyword then do
    if token.span.start.column /= 1
       then Left (ParseFailure token.span.start "export must start in column 1") else Right ()
    case rest of
      next :: _ => if next.kind == ExportKeyword then Left (ParseFailure next.span.start "Duplicate export marker") else Right ()
      [] => Right ()
    (item, remaining) <- parseOne budget end rest
    let start = case item of
          MutualItem group => group.span.start
          DataItem sourceData => sourceData.span.start
          Ordinary decl => decl.span.start
          RecordItem sourceRecord => sourceRecord.span.start
          InterfaceItem sourceRecord => sourceRecord.span.start
          ImplementationItem decl => decl.span.start
          ImplementationBlock block => block.span.start
    if start.line <= token.span.start.line
       then Left (ParseFailure start "export must precede the declaration on its own line") else Right ()
    let marked = case item of
          MutualItem group => MutualItem ({ exported := True, span := Between token.span.start group.span.finish } group)
          DataItem sourceData => DataItem ({ exported := True, span := Between token.span.start sourceData.span.finish } sourceData)
          Ordinary decl => Ordinary ({ exported := True, span := Between token.span.start decl.span.finish } decl)
          RecordItem sourceRecord => RecordItem ({ exported := True, span := Between token.span.start sourceRecord.span.finish } sourceRecord)
          InterfaceItem sourceRecord => InterfaceItem ({ exported := True, span := Between token.span.start sourceRecord.span.finish } sourceRecord)
          ImplementationItem decl => ImplementationItem ({ exported := True, span := Between token.span.start decl.span.finish } decl)
          ImplementationBlock block => ImplementationBlock ({ exported := True, span := Between token.span.start block.span.finish } block)
    Right (marked, remaining)
  else if token.kind == MutualKeyword then parseMutual budget end tokens
  else if token.kind == DataKeyword then parseData budget end tokens
  else if token.kind == RecordKeyword || token.kind == InterfaceKeyword then parseRecordLike token.kind budget end tokens
  else if token.kind == ImplementationKeyword then parseImplementation budget end tokens
  else do
    (decl, remaining) <- parsePair budget end tokens
    Right (Ordinary decl, remaining)
parseOne budget end [] = Left (ParseFailure end "Expected declaration")

admit : Nat -> List String -> List BindingSite -> Either ParseError (Nat, List String)
admit slots seen [] = Right (slots, seen)
admit Z seen (site :: _) = Left (ParseFailure site.nameSpan.start "Declaration count budget exhausted")
admit (S slots) seen (site :: rest) =
  if elem site.name seen then Left (ParseFailure site.nameSpan.start ("Duplicate declaration " ++ show site.name))
     else admit slots (site.name :: seen) rest

parseAll : Nat -> Nat -> Nat -> Position -> List String -> List Token ->
           Either ParseError (List AuthoredDeclaration)
parseAll fuel slots expressions end seen [] = Right []
parseAll Z slots expressions end seen tokens =
  Left (ParseFailure (nextPosition end tokens) "Declaration count budget exhausted")
parseAll (S fuel) slots expressions end seen tokens = do
  (item, remaining) <- parseOne expressions end tokens
  (slots, seen) <- admit slots seen (bindingSites item)
  rest <- parseAll fuel slots expressions end seen remaining
  Right (item :: rest)

||| Parse authored syntax only. Binding-site quotas do not generate definitions.
public export
parseAuthoredDeclarations : Nat -> Nat -> Position -> List Token ->
                            Either ParseError (List AuthoredDeclaration)
parseAuthoredDeclarations budget expressions end = parseAll budget budget expressions end []

||| Legacy ordinary-only adapter. Records require explicit authored parsing and
||| the separate elaborator; this grammar module has no elaborator dependency.
public export
parseDeclarations : Nat -> Nat -> Position -> List Token -> Either ParseError (List Declaration)
parseDeclarations budget expressions end tokens = do
  authored <- parseAuthoredDeclarations budget expressions end tokens
  if any requiresElaboration authored then Left (ParseFailure end "Records/interfaces/implementations require the authored document/elaboration pipeline")
     else Right (ordinaryDeclarations authored)

-- Synthetic entry reference is at EOF; all lowered let extents stay ordered.
-- Presence of main is checked before lowering; no source location is invented
-- for a core typing error or for a nonexistent entry.
legacyLowerDeclarations : Position -> List Declaration -> Expr
legacyLowerDeclarations end [] = NRef (Between end end) "main"
legacyLowerDeclarations end (decl :: rest) =
  NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
       (legacyLowerDeclarations end rest)

public export
declarationAhead : List Token -> Bool
declarationAhead (Located Name _ _ :: Located Colon _ _ :: _) = True
declarationAhead (Located Name _ _ :: Located Equals _ _ :: _) = True
declarationAhead (Located Number _ _ :: _) = True
declarationAhead (Located MutualKeyword _ _ :: _) = True
declarationAhead (Located DataKeyword _ _ :: _) = True
declarationAhead (Located RecordKeyword _ _ :: _) = True
declarationAhead (Located InterfaceKeyword _ _ :: _) = True
declarationAhead (Located ImplementationKeyword _ _ :: _) = True
declarationAhead (Located ExportKeyword _ _ :: _) = True
declarationAhead _ = False

||| Accept an expression or a nonrecursive declaration file with fixed main entry.
||| Declarations elaborate to existing typed lets; no new trusted core rule.
public export
parseSource : (declarationBudget, expressionBudget : Nat) -> Position ->
              List Token -> Either ParseError Expr
parseSource declarationBudget expressionBudget end tokens =
  if declarationAhead tokens then do
    declarations <- parseDeclarations declarationBudget expressionBudget end tokens
    if any generated declarations then Left (ParseFailure end "Records require a named module; use parseDocument") else Right ()
    if any (\decl => decl.exported) declarations
       then Left (ParseFailure end "export requires a named module; use parseDocument")
       else Right ()
    if any (\decl => decl.name == "main") declarations
       then Right (legacyLowerDeclarations end declarations)
       else Left (ParseFailure end "Declaration file requires a main definition")
  else parseExpression expressionBudget end tokens
