module UntypedLambdaCalculus.Subterm

import Decidable.Equality

import UntypedLambdaCalculus
import PathProof

%default total

data SubtermPath : Term -> Term -> Type where 
  AppFn: SubtermPath (Application fn arg) fn 
  AppArg: SubtermPath (Application fn arg) arg 
  AbsBody: SubtermPath (Abstraction param body) body 

next : (term: Term) -> List (subterm: Term ** SubtermPath term subterm)


||| A path proof that a certain term is a subterm of a term.
public export
Subterm : (subTerm, term: Term) -> Type
Subterm subTerm term = Any next (\term' => subTerm = term') term 

||| Decide whether a term is a subterm of another.
public export
isSubterm : (a, b: Term) -> Dec (Subterm a b)  
isSubterm a b = any next (decEq a) b 

||| A term is a subterm of itself.
public export
subtermReflexivity : (a: Term) -> Subterm a a
subtermReflexivity term = Here Refl 

||| Given a proof that `a` is a subterm of `b`, and a proof that `b` is a subterm of `c`,
||| derive a proof that `a` is also a subterm of `c`.
public export
subtermTransitivity : Subterm a b -> Subterm b c -> Subterm a c
subtermTransitivity aSubB (Here Refl) = aSubB
subtermTransitivity aSubB (There AppFn bSubFn) = There AppFn (subtermTransitivity aSubB bSubFn)
subtermTransitivity aSubB (There AppArg bSubArg) = There AppArg (subtermTransitivity aSubB bSubArg)
subtermTransitivity aSubB (There AbsBody bSubBody) = There AbsBody (subtermTransitivity aSubB bSubBody)
 
{-
||| If an `Application` is a subterm of some term, it's `fn`, is also a subterm of that term.
public export
appFnSubterm : Subterm (Application fn arg) term -> Subterm fn term
appFnSubterm prf = subtermTransitivity (There AppFn (Here Refl)) prf

||| If an `Application` is a subterm of some term, it's `arg`, is also a subterm of that term.
public export
appArgSubterm : Subterm (Application fn arg) term -> Subterm arg term
appArgSubterm prf = subtermTransitivity (There AppArg (Here Refl)) prf

||| If an `Abstraction` is a subterm of some term, it's `body`, is also a subterm of that term.
public export
absBodySubterm : Subterm (Abstraction param body) term -> Subterm body term
absBodySubterm prf = subtermTransitivity (There AbsBody (Here Refl)) prf

||| Variables are the smallest terms and therefore an Application cannot be a subterm.
public export
appNeverSubVar : Subterm (Application _ _) (Variable _) -> Void
appNeverSubVar (Here Refl) impossible

||| Variables are the smallest terms and therefore an Abstraction cannot be a subterm.
public export
absNeverSubVar : Subterm (Abstraction _ _) (Variable _) -> Void
absNeverSubVar (Here Refl) impossible

mutual
  ||| An Application cannot be a subterm of its own `fn` because that would require
  ||| an infinitely nested lambda expression.
  public export
  appNeverSubOwnFn : Subterm (Application fn arg) fn -> Void
  appNeverSubOwnFn (Here Refl) impossible
  appNeverSubOwnFn (There AppFn subFn) = appNeverSubOwnFn (appFnSubterm subFn)
  appNeverSubOwnFn (There AppArg subArg) = appNeverSubOwnArg (appFnSubterm subArg)
  appNeverSubOwnFn (There AbsBody subBody) = absNeverSubOwnBody (appFnSubterm subBody)

  ||| An Application cannot be a subterm of its own `arg` because that would require
  ||| an infinitely nested lamda expression. 
  public export
  appNeverSubOwnArg : Subterm (Application fn arg) arg -> Void
  appNeverSubOwnArg (Here Refl) impossible
  appNeverSubOwnArg (There AppFn subFn) = appNeverSubOwnFn (appArgSubterm subFn)
  appNeverSubOwnArg (There AppArg subArg) = appNeverSubOwnArg (appArgSubterm subArg)
  appNeverSubOwnArg (There AbsBody subBody) = absNeverSubOwnBody (appArgSubterm subBody)

  ||| An Abstraction cannot be a subterm of its own `body` because that would require
  ||| an infinitely nested lambda expression.
  public export
  absNeverSubOwnBody : Subterm (Abstraction param body) body -> Void
  absNeverSubOwnBody (Here Refl) impossible
  absNeverSubOwnBody (There AppFn subFn) = appNeverSubOwnFn (absBodySubterm subFn)
  absNeverSubOwnBody (There AppArg subArg) = appNeverSubOwnArg (absBodySubterm subArg)
  absNeverSubOwnBody (There AbsBody subBody) = absNeverSubOwnBody (absBodySubterm subBody)

||| If the terms in the subterm relation can be swapped around then they must be equal.
public export
subtermEqualWhenCommutative : Subterm a b -> Subterm b a -> a = b
subtermEqualWhenCommutative (Here Refl) bSubA = Refl
subtermEqualWhenCommutative (There AppFn subFn) bSubA =
  let (Refl) = subtermEqualWhenCommutative subFn (appFnSubterm bSubA)
  in absurd (appNeverSubOwnFn bSubA)  
subtermEqualWhenCommutative (There AppArg subArg) bSubA = 
  let (Refl) = subtermEqualWhenCommutative subArg (appArgSubterm bSubA)
  in absurd (appNeverSubOwnArg bSubA)
subtermEqualWhenCommutative (There AbsBody subBody) bSubA = 
  let (Refl) = subtermEqualWhenCommutative subBody (absBodySubterm bSubA)
  in absurd (absNeverSubOwnBody bSubA)

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
-}
