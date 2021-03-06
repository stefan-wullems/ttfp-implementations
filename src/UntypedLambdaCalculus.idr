module UntypedLambdaCalculus

import Data.List
import Decidable.Equality

public export
data Term : Type where
  Variable: (name: String) -> Term
  Application: (fn: Term) -> (arg: Term) -> Term
  Abstraction: (param: String) -> (body: Term) -> Term

%name Term t1, t2, t3, t4, t5

public export
Uninhabited (Variable _      = Application _ _) where uninhabited Refl impossible
public export
Uninhabited (Variable _      = Abstraction _ _) where uninhabited Refl impossible
public export
Uninhabited (Application _ _ = Variable _     ) where uninhabited Refl impossible
public export
Uninhabited (Application _ _ = Abstraction _ _) where uninhabited Refl impossible
public export
Uninhabited (Abstraction _ _ = Variable _     ) where uninhabited Refl impossible
public export
Uninhabited (Abstraction _ _ = Application _ _) where uninhabited Refl impossible

public export
DecEq Term where
  decEq (Variable name) (Variable name') = 
    case decEq name name' of
      Yes Refl => 
        Yes Refl

      No nameNeq => 
        No (\Refl => nameNeq Refl) 
  decEq (Variable name) (Application fn arg) = No absurd
  decEq (Variable name) (Abstraction param body) = No absurd
  decEq (Application fn arg) (Variable name) = No absurd
  decEq (Application fn arg) (Application fn' arg') = 
    case decEq (fn, arg) (fn', arg') of
      Yes Refl => 
        Yes Refl

      No appNeq => 
        No (\Refl => appNeq Refl)
  decEq (Application fn arg) (Abstraction param body) = No absurd
  decEq (Abstraction param body) (Variable name) = No absurd
  decEq (Abstraction param body) (Application fn arg) = No absurd
  decEq (Abstraction param body) (Abstraction param' body') = 
    case decEq (param, body) (param', body') of
      Yes Refl => 
        Yes Refl

      No absNeq => 
        No (\Refl => absNeq Refl)

public export
Eq Term where
  (==) t1 t2 = 
    case decEq t1 t2 of
      Yes prf => 
        True
      
      No t1NeqT2 =>
        False

||| List the subterms of a term.
public export
listSubterms : Term -> List Term
listSubterms var@(Variable name) = [var]
listSubterms app@(Application fn arg) = app :: listSubterms fn ++ listSubterms arg
listSubterms abs@(Abstraction param body) = abs :: listSubterms body

||| How often does a term occur within another term?
public export
countOccurrences : (subterm: Term) -> (term: Term) -> Nat
countOccurrences subterm term@(Variable name) = if term == subterm then 1 else 0
countOccurrences subterm term@(Application fn arg) =
  let subOccurrences = countOccurrences subterm fn + countOccurrences subterm arg
  in
    if term == subterm then
      subOccurrences + 1
    else
      subOccurrences
countOccurrences subterm term@(Abstraction param body) =
  let subOccurrences = countOccurrences subterm body
  in
    if term == subterm then
       subOccurrences + 1
    else
       subOccurrences

freeVariables : Term -> List String
freeVariables (Variable name) = [name]
freeVariables (Application fn arg) = union (freeVariables fn) (freeVariables arg)
freeVariables (Abstraction param body) = delete param (freeVariables body)

