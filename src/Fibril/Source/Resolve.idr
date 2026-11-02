-- Compatibility facade. Contextual expression elaboration lives outside grammar.
module Fibril.Source.Resolve

import Data.Vect
import Fibril.Core.Term
import Fibril.Source.Syntax
import Fibril.Source.Global
import public Fibril.Source.Resolve.Error
import Fibril.Elaboration.Expression

%default total

||| Lexical compatibility API: arbitrary name vectors provide no typed context.
public export
resolveInWith : List GlobalDefinition -> Vect n String -> Expr -> Either ResolveError (Term n)
resolveInWith globals = elaborateInWith globals Nothing

public export
resolveIn : Vect n String -> Expr -> Either ResolveError (Term n)
resolveIn = resolveInWith []

public export
resolveClosedWith : List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
resolveClosedWith = elaborateClosedWith

public export
resolveClosed : Expr -> Either ResolveError (Term 0)
resolveClosed = elaborateClosed
