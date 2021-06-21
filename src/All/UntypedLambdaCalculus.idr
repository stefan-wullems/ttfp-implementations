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

-- @Todo: can I get rid of this?
elemNeqSingleton : Elem x [y] -> Not (x = y) -> Void
elemNeqSingleton Here contra = contra Refl
elemNeqSingleton { x, y} (There z) contra = absurd z

-- @Todo: can I get rid of this?
elemNeqHead : {ys: List a} -> Elem x (y :: ys) -> Not (x = y) -> Elem x ys
elemNeqHead {ys = []} prf prfNeq = absurd $ elemNeqSingleton prf prfNeq
elemNeqHead {ys = (z :: xs)} prf prfNeq = elemNeqHead prf prfNeq

-- @Todo: can I get rid of this?
elemSingleton : Elem x [x'] -> x = x'
elemSingleton Here = Refl
elemSingleton (There y) = absurd y

abstractionSubterm : {t: Term} -> Elem (Abstraction v t') (subterms t) -> Elem t' (subterms t)
abstractionSubterm {t = Variable y} x impossible
abstractionSubterm {t = Application y z} (There x) =
  case elemAppLorR (subterms y) (subterms z) x of
    Left appSubY => 
      There (elemAppLeft (subterms y) (subterms z) (abstractionSubterm appSubY))
       
    Right appSubZ =>
      There (elemAppRight (subterms y) (subterms z) (abstractionSubterm appSubZ))

abstractionSubterm {t = Abstraction v t'} Here = There (isSubtermReflexivity t') 
abstractionSubterm {t = Abstraction x y} (There z) = There (abstractionSubterm z)

applicationSubterm : {t: Term} -> Elem (Application t1' t2') (subterms t) -> (Elem t1' (subterms t), Elem t2' (subterms t))
applicationSubterm {t = Variable y} x impossible 
applicationSubterm {t = Application t1' t2'} Here = 
  ( There (elemAppLeft (subterms t1') (subterms t2') (isSubtermReflexivity t1')) 
  , There (elemAppRight (subterms t1') (subterms t2') (isSubtermReflexivity t2'))
  ) 
applicationSubterm {t = Application y z} (There x) = 
  case elemAppLorR (subterms y) (subterms z) x of
    Left w => 
      let (t1SubY, t2SubY) = applicationSubterm w
      in 
        ( There (elemAppLeft (subterms y) (subterms z) t1SubY) 
        , There (elemAppLeft (subterms y) (subterms z) t2SubY)
        )

    Right w => 
     let (t1SubZ, t2SubZ) = applicationSubterm w
     in 
       ( There (elemAppRight (subterms y) (subterms z) t1SubZ) 
       , There (elemAppRight (subterms y) (subterms z) t2SubZ)
       )

applicationSubterm {t = Abstraction y z} (There x) = bimap There There (applicationSubterm x) 

mutual
  abstractionIH : {t1, t2, t3: Term} -> {auto prfAbstraction: t2 = Abstraction _ _} -> Elem t1 (subterms t2) -> Elem t2 (subterms t3) -> Dec (t1 = t2) -> Elem t1 (subterms t3)
  abstractionIH {prfAbstraction=Refl} t1SubAbs absSubT2 (Yes Refl) = absSubT2
  abstractionIH {prfAbstraction=Refl} t1SubAbs absSubT2 (No contra) = 
    let t1SubT = elemNeqHead t1SubAbs contra
        tSubT3 = abstractionSubterm absSubT2
    in subtermElemTransitivity t1SubT tSubT3

  applicationIH : {t1, t2, t3: Term} -> {auto prfApplication: t2 = Application ap1 ap2} -> Elem t1 (subterms t2) -> Elem t2 (subterms t3) -> Dec (t1 = t2) -> Elem t1 (subterms t3)
  applicationIH {prfApplication=Refl} t1SubT2 t2SubT3 (Yes Refl) = t2SubT3
  applicationIH {prfApplication=Refl} t1SubT2 t2SubT3 (No contra) = 
    let (ap1SubT3, ap2SubT3) = applicationSubterm t2SubT3
    in 
      case elemAppLorR (subterms ap1) (subterms ap2) (elemNeqHead t1SubT2 contra) of
        Left t1SubAp1 => 
          subtermElemTransitivity t1SubAp1 ap1SubT3   
        
        Right t1SubAp2 => 
          subtermElemTransitivity t1SubAp2 ap2SubT3

  subtermElemTransitivity : {t1, t2, t3: Term} -> Elem t1 (subterms t2) -> Elem t2 (subterms t3) -> Elem t1 (subterms t3)
  subtermElemTransitivity {t1, t2, t3} t1SubT2 t2SubT3 = 
    case t1 of
      Variable x => 
        case t2 of
          Variable v' => 
            rewrite elemSingleton t1SubT2 in t2SubT3

          Application t1' t2' => 
            applicationIH t1SubT2 t2SubT3 (No uninhabited)

          Abstraction v' t' => 
            abstractionIH t1SubT2 t2SubT3 (No uninhabited)

      Application x y => 
        case t2 of
          Variable v' => 
            absurd t1SubT2
        
          Application t1' t2' =>
            applicationIH t1SubT2 t2SubT3 (decEq (Application x y) t2)

          Abstraction v' t' =>
            abstractionIH t1SubT2 t2SubT3 (No uninhabited)

      Abstraction x y => 
        case t2 of
          Variable v =>
            absurd t1SubT2
        
          Application t1' t2' => 
            applicationIH t1SubT2 t2SubT3 (No uninhabited)

          Abstraction v' t' => 
            abstractionIH t1SubT2 t2SubT3 (decEq (Abstraction x y) t2)
