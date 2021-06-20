module All.UntypedLambdaCalculus

import Data.List.Elem
import Data.List.Elem.Extra
import Decidable.Equality

data Term 
  = Variable String
  | Application Term Term
  | Abstraction String Term

Uninhabited (Variable _      = Application _ _) where uninhabited Refl impossible
Uninhabited (Variable _      = Abstraction _ _) where uninhabited Refl impossible
Uninhabited (Application _ _ = Variable _     ) where uninhabited Refl impossible
Uninhabited (Application _ _ = Abstraction _ _) where uninhabited Refl impossible
Uninhabited (Abstraction _ _ = Variable _     ) where uninhabited Refl impossible
Uninhabited (Abstraction _ _ = Application _ _) where uninhabited Refl impossible

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

subterms : Term -> List Term
subterms var@(Variable x) = [var]
subterms app@(Application x y) = app :: subterms x ++ subterms y
subterms abs@(Abstraction x y) = abs :: subterms y

isSubterm : (a: Term) -> (b: Term) -> Dec (Elem b (subterms a))  
isSubterm a b = isElem b (subterms a)

isSubtermReflexivity : (a: Term) -> Elem a (subterms a)
isSubtermReflexivity a = 
  case isSubterm a a of
    Yes prf => prf
    No contra => 
      case a of
        Variable x => Here
        Application x y => Here
        Abstraction x y => Here

Uninhabited (Elem (Application t1 t2) (subterms (Variable v))) where
  uninhabited heyy impossible

Uninhabited (Elem (Abstraction v1 t2) (subterms (Variable v2))) where
  uninhabited heyy impossible

elemNeqSingleton : {x, y: a} -> Elem x [y] -> Not (y = x) -> Void
elemNeqSingleton Here contra = contra Refl
elemNeqSingleton { x, y} (There z) contra = absurd z

elemNeqHead : {x, y: a} -> {ys: List a} -> Elem x (y :: ys) -> Not (y = x) -> Elem x ys
elemNeqHead {x = x} {y = y} {ys = []} prf prfNeq = absurd $ elemNeqSingleton prf prfNeq
elemNeqHead {x = x} {y = y} {ys = (z :: xs)} prf prfNeq = elemNeqHead prf prfNeq

elemAppLorR': {xs, ys : List a}
           -> (prf : Elem k (xs ++ ys))
           -> Either (Elem k xs) (Elem k ys)
elemAppLorR' {xs} {ys} = elemAppLorR xs ys

elemSingleton : Elem x [x'] -> x = x'
elemSingleton Here = Refl
elemSingleton (There y) = absurd y

abstractionSubterm : Elem (Abstraction v t') (subterms t) -> Elem t' (subterms t)

applicationSubterm : Elem (Application t1' t2') (subterms t) -> (Elem t1' (subterms t), Elem t2' (subterms t)) 


mutual
  variableTransitive : {t1, t2: Term} -> Elem (Variable v) (subterms t1) -> Elem t1 (subterms t2) -> Elem (Variable v) (subterms t2)
  variableTransitive {t1, t2} varSubT1 t1SubT2 = 
    case t1 of
      -- Being a subterm of a Variable means being equal to that Variable
      Variable v' => 
        case elemSingleton varSubT1 of 
          Refl => 
            t1SubT2

      Application t1' t2' => ?whatt_2
      Abstraction v' t' => ?whatt_3

  applicationTransitive : {t1, t2: Term} -> Elem (Application t1' t2') (subterms t1) -> Elem t1 (subterms t2) -> Elem (Application t1' t2') (subterms t2)
  applicationTransitive {t1, t2} appSubT1 t1SubT2 =
    case t1 of
      -- Makes no sense to have an Application as a subterm to a variable
      Variable v' => 
        absurd appSubT1
      
      Application t1' t2' => ?whattt_2
      Abstraction v' t' => ?whattt_3

  abstractionTransitive : {t1, t2, t3: Term} -> {auto prfAbstraction: t1 = Abstraction _ _} -> Elem t1 (subterms t2) -> Elem t2 (subterms t3) -> Elem t1 (subterms t3)
  abstractionTransitive  {t1=Abstraction v t, t2, t3} {prfAbstraction=Refl}  t1SubT2 t2SubT3 =
    case t2 of
      -- Makes no sense to have an Abstraction as a subterm to a variable
      Variable v =>
        absurd t1SubT2
      
      Application t1' t2' => ?whattt_4

      -- Induction step using abstractionTransitive
      Abstraction v' t' => 
        case decEq t2 (Abstraction v t) of
          -- if t1 = t2 we just return the proof for t2 because it will also apply to t1
          Yes Refl => t2SubT3
          -- if Not (t1 = t2) we apply the induction hypothesis. 
          No contra => 
            let t1SubT = elemNeqHead t1SubT2 contra
                tSubT3 = abstractionSubterm t2SubT3
            in abstractionTransitive t1SubT tSubT3
            


  subtermElemTransitivity : {a, b, c: Term} -> Elem b (subterms a) -> Elem c (subterms b) -> Elem c (subterms a)
  subtermElemTransitivity {a} {b} {c} bSubA cSubB =
    case c of
      Variable x => variableTransitive cSubB bSubA
      Application x y => applicationTransitive cSubB bSubA
      Abstraction x y => abstractionTransitive cSubB bSubA