module All.UntypedLambdaCalculus

import Data.List.Elem
import Data.OneOf
import Data.List.Elem.Extra
import Decidable.Equality

data Term : Type where
  Variable: (name: String) -> Term
  Application: (fn: Term) -> (arg: Term) -> Term
  Abstraction: (param: String) -> (body: Term) -> Term

%name Term t1, t2, t3, t4, t5

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

data Subterm: (subTerm, term: Term) -> Type where
  Here: Subterm term term
  ThereAppFn: (Subterm subTerm fn) -> Subterm subTerm (Application fn arg)
  ThereAppArg: (Subterm subTerm arg) -> Subterm subTerm (Application fn arg)
  ThereAbsBody: (Subterm subTerm body) -> Subterm subTerm (Abstraction param body)

||| Decide whether a term is a subterm of another.
isSubterm : (a, b: Term) -> Dec (Subterm a b)  
isSubterm a b = 
  case decEq a b of
    Yes Refl =>
      -- Because the subterm relation is reflexive, if `a` equals `b`, then it's a subterm of `b`.
      Yes Here

    No aNeqB =>
      case b of
        Variable name =>
          -- Given `a \= b` and `b = Variable name`, we know enough to say that `a` is not a subterm of `b`.  
          -- `Variables` only have themselves as subterms.   
          No (\Here => aNeqB Refl)

        Application fn arg =>
          -- Given `a \= b` and `b = Application fn arg`. For `a` to be a subterm of `b` it must either be a subterm of `fn` or `arg`.
          case isSubterm a fn of
            Yes aSubFn =>
              -- `a` was found to be a subterm of `fn`. Therefore it is also a subterm of `b`.
              Yes (ThereAppFn aSubFn)

            No aNsubFn =>
              -- `a` is not a subterm of `fn`, but it can still be a subterm of `b` if it is a subterm of `arg`.
              case isSubterm a arg of
                 Yes aSubArg =>
                   -- `a` was found to be a subterm of `arg`. Therefore it is also a subterm of `b`.
                   Yes (ThereAppArg aSubArg)

                 No aNsubArg =>
                   -- We know enough to say that `a` is not a subterm of `b` because:
                   No (\aSubB => 
                    case aSubB of 
                      Here =>
                        -- `a` is not equal to `b`,
                        aNeqB Refl

                      ThereAppFn aSubFn =>
                        -- nor is it a subterm of `fn`,
                        aNsubFn aSubFn

                      ThereAppArg aSubArg =>
                        -- nor is it a subterm of `arg`.
                        aNsubArg aSubArg 
                   )  

        Abstraction param body =>
          -- Given `a \= b` and `b = Abstraction param body`. For `a` to be a subterm of `b` it must be a subterm of `body`. 
          case isSubterm a body of
            Yes aSubBody => 
              -- `a` was found to be a subterm of `body`. Therefore it is also a subterm of `b`.
              Yes (ThereAbsBody aSubBody)

            No aNsubBody =>
              -- We know enough to say that `a` is not a subterm of `b` because:
              No (\aSubB => 
                case aSubB of
                  Here =>
                    -- `a` is not equal to `b`,
                    aNeqB Refl

                  ThereAbsBody aSubBody =>
                    -- nor is it a subterm of `body`.
                    aNsubBody aSubBody
              )

subtermReflexivity : (term: Term) -> Subterm a a
subtermReflexivity term  = Here 

Uninhabited (Elem (Application t1 t2) (subterms (Variable v))) where uninhabited prf impossible
Uninhabited (Elem (Abstraction v1 t2) (subterms (Variable v2))) where uninhabited prf impossible

elemSingleton : Elem x [x'] -> x = x'
elemSingleton Here = Refl
elemSingleton (There y) = absurd y

--termElemSubtermElem : {parentTerm, term, subTerm: Term} -> 
--                      { auto subtermCase: Subterm term subTerm } -> 
--                      Elem term (subterms parentTerm) -> 
--                      Elem subTerm (subterms parentTerm)
--termElemSubtermElem {parentTerm, term, subTerm} t1SubT2 {subtermCase} = ?blaaaa

--abstractionSubterm : {t1, t2: Term} -> 
--                     {auto t1Abs: t1 = Abstraction t1Param t1Body} -> 
--                     Elem t1 (subterms t2) -> Elem t1Body (subterms t2)
--abstractionSubterm {t1 = Abstraction t1Param t1Body, t2} {t1Abs=Refl} t1SubT2 =
--  case t2 of
--    Variable name =>
--       -- An Abstraction cannot be a subterm of a Variable because variables have no subterms other than themselves.             
--      absurd t1SubT2

--    Application fn arg =>
--      case t1SubT2 of
--        There t1SubFnOrArg =>
--          case elemAppLorR _ _ t1SubFnOrArg of
--            Left appSubFn => 
--              There $ elemAppLeft _ _ (abstractionSubterm appSubFn)
--       
--            Right appSubArg =>
--              There $ elemAppRight _ _ (abstractionSubterm appSubArg)
--
--    Abstraction t2Param t2Body =>
--      case t1SubT2 of
--        Here =>
--          There $ subtermReflexivity t2Body
--
--        There t1SubT2Body =>
--          There $ abstractionSubterm t1SubT2Body
--
--applicationSubtermHelp : {t, t1, t2: Term} -> 
--                         { auto t1App: t1 = Application t1Fn t1Arg } -> 
--                         { auto tFnOrArg: Either (t = t1Fn) (t = t1Arg) } ->
--                         Elem t1 (subterms t2) -> 
--                         Elem t (subterms t2)
--applicationSubtermHelp {t1 = Application t1Fn t1Arg, t2} {t1App=Refl} {tFnOrArg} t1SubT2 = 
--  case t2 of
--    Variable name =>
--      -- An Application cannot be a subterm of a Variable because variables have no subterms other than themselves. 
--      absurd t1SubT2
--      
--    Application t2Fn t2Arg =>
--      case t1SubT2 of
--        Here =>
--          -- In this case t1 = t2, so now we show that t is a subterm to t1.
----------          case tFnOrArg of
--            Left Refl => 
--              There $ elemAppLeft _ _ (subtermReflexivity t2Fn)
--      
--            Right Refl => 
--              There $ elemAppRight _ _ (subtermReflexivity t2Arg)
--        
--        There t1SubT2FnOrArg =>
--          -- In this case, t1 can be found somewhere later in the subterms of t2. 
--          case elemAppLorR _ _ t1SubT2FnOrArg of
--            Left t1SubT2Fn =>
--              There $ elemAppLeft _ _ (applicationSubtermHelp t1SubT2Fn)

--            Right t1SubT2Arg =>
--              There $ elemAppRight _ _ (applicationSubtermHelp t1SubT2Arg) 

--    Abstraction name body =>
--      case t1SubT2 of
--        There t1SubT =>
--          -- (t1 \= t2) because t2 is an Abstraction. Therefore t1 must be in the subterms of t2.
--          There $ applicationSubtermHelp t1SubT
--
--applicationSubterm : {t1, t2: Term} -> {auto t1App: t1 = Application t1Fn t1Arg} -> Elem t1 (subterms t2) -> (Elem t1Fn (subterms t2), Elem t1Arg (subterms t2))
--applicationSubterm appSubT2 {t1App=Refl} = 
--  ( applicationSubtermHelp {t=t1Fn} appSubT2
--  , applicationSubtermHelp {t=t1Arg} appSubT2
--  )

--subtermElemTransitivity : {t1, t2, t3: Term} -> Elem t1 (subterms t2) -> Elem t2 (subterms t3) -> Elem t1 (subterms t3)
--subtermElemTransitivity {t1, t2, t3} t1SubT2 t2SubT3 = 
--  case t2 of
--    Variable x =>
--      case t1 of
--        Variable v' => 
--          rewrite elemSingleton t1SubT2 in t2SubT3
--
--        Application t1' t2' =>
--          -- An Application cannot be a subterm of a Variable because variables have no subterms other than themselves. 
--          absurd t1SubT2
--
--        Abstraction v' t' =>
--          -- An Abstraction cannot be a subterm of a Variable because variables have no subterms other than themselves. 
--          absurd t1SubT2
--
--    Application x y =>
--      case t1SubT2 of
--        Here =>
--         t2SubT3
--
--        There t1SubT2FnOrArg =>
--          let (t2FnSubT3, t2ArgSubT3) = applicationSubterm t2SubT3
--          in 
--            case elemAppLorR _ _ t1SubT2FnOrArg of
--              Left t1SubT2Fn => 
--                subtermElemTransitivity t1SubT2Fn t2FnSubT3   
--        
--              Right t1SubT2Arg => 
--                subtermElemTransitivity t1SubT2Arg t2ArgSubT3

--    Abstraction param body =>
--      case t1SubT2 of
--        Here =>
--          t2SubT3

--        There t1SubT =>
--          subtermElemTransitivity t1SubT (abstractionSubterm t2SubT3)
