module UntypedLambdaCalculus

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
