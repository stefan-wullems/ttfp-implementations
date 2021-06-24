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

-- @TODO cleanup
public export
DecEq Term where
  decEq (Variable x) (Variable y) = 
    case decEq x y of
      Yes Refl => Yes Refl
      No contra => No (\Refl => contra Refl) 
  decEq (Variable x) (Application y z) = No absurd
  decEq (Variable x) (Abstraction y z) = No absurd
  decEq (Application x y) (Variable z) = No absurd
  decEq (Application x y) (Application z w) = 
    case decEq (x, y) (z, w) of
      Yes Refl => Yes Refl
      No contra => No (\Refl => contra Refl)
  decEq (Application x y) (Abstraction z w) = No absurd
  decEq (Abstraction x y) (Variable z) = No absurd
  decEq (Abstraction x y) (Application z w) = No absurd
  decEq (Abstraction x y) (Abstraction z w) = 
    case decEq (x, y) (z, w) of
      Yes Refl => Yes Refl
      No contra => No (\Refl => contra Refl)
