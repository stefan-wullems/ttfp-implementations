module UntypedLambdaCalculus.Combinator

import Data.List
import Data.List.Elem

import Decidable.Equality

import UntypedLambdaCalculus

||| A combinator is a term without any free variables.
IsCombinator : Term -> Type
IsCombinator term = freeVariables term = []

isCombinator : (term: Term) -> Dec (IsCombinator term)
isCombinator term = decEq (freeVariables term) []
