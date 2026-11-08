module PureDefinitionWrongReembedding

import Data.Vect
import Fibril.Core.Term
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.CoreTranslation
import Fibril.Cubical.Source.PureDefinition

bad : PureImage [] BoolFalse
bad = Image BoolTy (Boolean True) ABoolean Refl
