module UntypedLambdaCalculus.Subterm

import Decidable.Equality

import public UntypedLambdaCalculus

subterms : Term -> List Term
subterms var@(Variable x) = [var]
subterms app@(Application x y) = app :: subterms x ++ subterms y
subterms abs@(Abstraction x y) = abs :: subterms y

data Subterm: (subTerm, term: Term) -> Type where
  Here: Subterm term term
  ThereAppFn: (Subterm subTerm fn) -> Subterm subTerm (Application fn arg)
  ThereAppArg: (Subterm subTerm arg) -> Subterm subTerm (Application fn arg)
  ThereAbsBody: (Subterm subTerm body) -> Subterm subTerm (Abstraction param body)

Uninhabited (Subterm (Application _ _) (Variable _)) where uninhabited prf impossible
Uninhabited (Subterm (Abstraction _ _) (Variable _)) where uninhabited prf impossible

||| A term is a subterm of itself
subtermReflexivity : (term: Term) -> Subterm a a
subtermReflexivity term = Here 

||| Decide whether a term is a subterm of another.
isSubterm : (a, b: Term) -> Dec (Subterm a b)  
isSubterm a b = 
  case decEq a b of
    Yes Refl =>
      -- Because the subterm relation is reflexive, if `a` equals `b`, then it's a subterm of `b`.
      Yes (subtermReflexivity a)

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

||| Given a proof that `a` is a subterm of `b` and a proof that `c` is a subterm of `a`,
||| derive a proof that `c`, the subterm of `a`, is also a subterm of `b`.
append: Subterm a b -> Subterm c a -> Subterm c b
append Here prfB = prfB
append (ThereAppFn later) prfB = ThereAppFn (append later prfB)
append (ThereAppArg later) prfB = ThereAppArg (append later prfB)
append (ThereAbsBody later) prfB = ThereAbsBody (append later prfB)

||| If an `Application` is a subterm of some term, it's `fn`, is also a subterm of that term.
appFnSubterm : Subterm (Application fn arg) term -> Subterm fn term
appFnSubterm prf = append prf (ThereAppFn Here)

||| If an `Application` is a subterm of some term, it's `arg`, is also a subterm of that term.
appArgSubterm : Subterm (Application fn arg) term -> Subterm arg term
appArgSubterm prf = append prf (ThereAppArg Here)

||| If an `Abstraction` is a subterm of some term, it's `body`, is also a subterm of that term.
absBodySubterm : Subterm (Abstraction param body) term -> Subterm body term
absBodySubterm prf = append prf (ThereAbsBody Here)

||| Given a proof that `a` is a subterm of `b`, and a proof that `b` is a subterm of `c`,
||| derive a proof that `a` is also a subterm of `c`.
subtermTransitivity : Subterm a b -> Subterm b c -> Subterm a c 
subtermTransitivity aSubB bSubC =
 case aSubB of
    Here =>
      -- Since we know that `a = b`, we know that the path from `a` to `c`, and `b` to `c` must be the same.
      -- We can therefore reutilize the path from `b` to `c` as the path from `a` to `c`.                           
      bSubC

    ThereAppFn aSubFn =>
      -- Induce that there is a path from `a` to `c` through `fn`.
      let fnSubC = appFnSubterm bSubC 
      in subtermTransitivity aSubFn fnSubC

    ThereAppArg aSubArg =>
      -- Induce that there is a path from `a` to `c` through `arg`.
      let argSubC = appArgSubterm bSubC
      in subtermTransitivity aSubArg argSubC

    ThereAbsBody aSubBody =>
      -- Induce that there is a path from `a` to `c` through `body`.
      let bodySubC = absBodySubterm bSubC
      in subtermTransitivity aSubBody bodySubC

