module UntypedLambdaCalculus.Subterm

import Decidable.Equality

import public UntypedLambdaCalculus

%default total

||| A path proof that a certain term is a subterm of a term.
public export
data Subterm: (subTerm, term: Term) -> Type where
  Here: Subterm term term
  ThereAppFn: (subFn: Subterm subTerm fn) -> Subterm subTerm (Application fn arg)
  ThereAppArg: (subArg: Subterm subTerm arg) -> Subterm subTerm (Application fn arg)
  ThereAbsBody: (subBody: Subterm subTerm body) -> Subterm subTerm (Abstraction param body)

||| A term is a subterm of itself.
public export
subtermReflexivity : (term: Term) -> Subterm a a
subtermReflexivity term = Here 

||| Given a proof that `a` is a subterm of `b`, and a proof that `b` is a subterm of `c`,
||| derive a proof that `a` is also a subterm of `c`.
public export
subtermTransitivity : Subterm a b -> Subterm b c -> Subterm a c
subtermTransitivity aSubB Here = aSubB
subtermTransitivity aSubB (ThereAppFn bSubFn) = ThereAppFn (subtermTransitivity aSubB bSubFn)
subtermTransitivity aSubB (ThereAppArg bSubArg) = ThereAppArg (subtermTransitivity aSubB bSubArg)
subtermTransitivity aSubB (ThereAbsBody bSubBody) = ThereAbsBody (subtermTransitivity aSubB bSubBody)
 
||| If an `Application` is a subterm of some term, it's `fn`, is also a subterm of that term.
public export
appFnSubterm : Subterm (Application fn arg) term -> Subterm fn term
appFnSubterm prf = subtermTransitivity (ThereAppFn Here) prf

||| If an `Application` is a subterm of some term, it's `arg`, is also a subterm of that term.
public export
appArgSubterm : Subterm (Application fn arg) term -> Subterm arg term
appArgSubterm prf = subtermTransitivity (ThereAppArg Here) prf

||| If an `Abstraction` is a subterm of some term, it's `body`, is also a subterm of that term.
public export
absBodySubterm : Subterm (Abstraction param body) term -> Subterm body term
absBodySubterm prf = subtermTransitivity (ThereAbsBody Here) prf

||| Decide whether a term is a subterm of another.
public export
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

||| Variables are the smallest terms and therefore an Application cannot be a subterm.
public export
appNeverSubVar : Subterm (Application _ _) (Variable _) -> Void
appNeverSubVar appSubVar impossible

||| Variables are the smallest terms and therefore an Abstraction cannot be a subterm.
public export
absNeverSubVar : Subterm (Abstraction _ _) (Variable _) -> Void
absNeverSubVar absSubVar impossible

mutual
  ||| An Application cannot be a subterm of its own `fn` because that would require
  ||| an infinitely nested lambda expression.
  public export
  appNeverSubOwnFn : Subterm (Application fn arg) fn -> Void
  appNeverSubOwnFn Here impossible
  appNeverSubOwnFn (ThereAppFn subFn) = appNeverSubOwnFn (appFnSubterm subFn)
  appNeverSubOwnFn (ThereAppArg subArg) = appNeverSubOwnArg (appFnSubterm subArg)
  appNeverSubOwnFn (ThereAbsBody subBody) = absNeverSubOwnBody (appFnSubterm subBody)

  ||| An Application cannot be a subterm of its own `arg` because that would require
  ||| an infinitely nested lamda expression. 
  public export
  appNeverSubOwnArg : Subterm (Application fn arg) arg -> Void
  appNeverSubOwnArg Here impossible
  appNeverSubOwnArg (ThereAppFn subFn) = appNeverSubOwnFn (appArgSubterm subFn)
  appNeverSubOwnArg (ThereAppArg subArg) = appNeverSubOwnArg (appArgSubterm subArg)
  appNeverSubOwnArg (ThereAbsBody subBody) = absNeverSubOwnBody (appArgSubterm subBody)

  ||| An Abstraction cannot be a subterm of its own `body` because that would require
  ||| an infinitely nested lambda expression.
  public export
  absNeverSubOwnBody : Subterm (Abstraction param body) body -> Void
  absNeverSubOwnBody Here impossible
  absNeverSubOwnBody (ThereAppFn subFn) = appNeverSubOwnFn (absBodySubterm subFn)
  absNeverSubOwnBody (ThereAppArg subArg) = appNeverSubOwnArg (absBodySubterm subArg)
  absNeverSubOwnBody (ThereAbsBody subBody) = absNeverSubOwnBody (absBodySubterm subBody)

public export
Uninhabited (Subterm (Application _ _) (Variable _)) where uninhabited = appNeverSubVar
public export
Uninhabited (Subterm (Abstraction _ _) (Variable _)) where uninhabited = absNeverSubVar

public export
Uninhabited (Subterm (Application fn arg) fn) where uninhabited = appNeverSubOwnFn
public export
Uninhabited (Subterm (Application fn arg) arg) where uninhabited = appNeverSubOwnArg
public export
Uninhabited (Subterm (Abstraction param body) body) where uninhabited = absNeverSubOwnBody

||| If the terms in the subterm relation can be swapped around then they must be equal.
public export
subtermEqualWhenCommutative : Subterm a b -> Subterm b a -> a = b
subtermEqualWhenCommutative Here bSubA = Refl
subtermEqualWhenCommutative (ThereAppFn subFn) bSubA =
  let (Refl) = subtermEqualWhenCommutative subFn (appFnSubterm bSubA)
  in absurd bSubA  
subtermEqualWhenCommutative (ThereAppArg subArg) bSubA = 
  let (Refl) = subtermEqualWhenCommutative subArg (appArgSubterm bSubA)
  in absurd bSubA
subtermEqualWhenCommutative (ThereAbsBody subBody) bSubA = 
  let (Refl) = subtermEqualWhenCommutative subBody (absBodySubterm bSubA)
  in absurd bSubA
