module UntypedLambdaCalculus.Subterm

import Decidable.Equality

import UntypedLambdaCalculus
import UntypedLambdaCalculus.Quantifiers

%default total

||| A path proof that a certain term is a subterm of a term.
public export
Subterm : (subTerm, term: Term) -> Type
Subterm subTerm term = Any (\term' => subTerm = term') term 

||| A term is a subterm of itself.
public export
subtermReflexivity : (a: Term) -> Subterm a a
subtermReflexivity term = Here Refl 

||| Given a proof that `a` is a subterm of `b`, and a proof that `b` is a subterm of `c`,
||| derive a proof that `a` is also a subterm of `c`.
public export
subtermTransitivity : Subterm a b -> Subterm b c -> Subterm a c
subtermTransitivity aSubB (Here Refl) = aSubB
subtermTransitivity aSubB (ThereAppFn bSubFn) = ThereAppFn (subtermTransitivity aSubB bSubFn)
subtermTransitivity aSubB (ThereAppArg bSubArg) = ThereAppArg (subtermTransitivity aSubB bSubArg)
subtermTransitivity aSubB (ThereAbsBody bSubBody) = ThereAbsBody (subtermTransitivity aSubB bSubBody)
 
||| If an `Application` is a subterm of some term, it's `fn`, is also a subterm of that term.
public export
appFnSubterm : Subterm (Application fn arg) term -> Subterm fn term
appFnSubterm prf = subtermTransitivity (ThereAppFn (Here Refl)) prf

||| If an `Application` is a subterm of some term, it's `arg`, is also a subterm of that term.
public export
appArgSubterm : Subterm (Application fn arg) term -> Subterm arg term
appArgSubterm prf = subtermTransitivity (ThereAppArg (Here Refl)) prf

||| If an `Abstraction` is a subterm of some term, it's `body`, is also a subterm of that term.
public export
absBodySubterm : Subterm (Abstraction param body) term -> Subterm body term
absBodySubterm prf = subtermTransitivity (ThereAbsBody (Here Refl)) prf

||| Decide whether a term is a subterm of another.
public export
isSubterm : (a, b: Term) -> Dec (Subterm a b)  
isSubterm a b = any (decEq a) b 

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
  appNeverSubOwnFn (ThereAppFn subFn) = appNeverSubOwnFn (appFnSubterm subFn)
  appNeverSubOwnFn (ThereAppArg subArg) = appNeverSubOwnArg (appFnSubterm subArg)
  appNeverSubOwnFn (ThereAbsBody subBody) = absNeverSubOwnBody (appFnSubterm subBody)

  ||| An Application cannot be a subterm of its own `arg` because that would require
  ||| an infinitely nested lamda expression. 
  public export
  appNeverSubOwnArg : Subterm (Application fn arg) arg -> Void
  appNeverSubOwnArg (Here Refl) impossible
  appNeverSubOwnArg (ThereAppFn subFn) = appNeverSubOwnFn (appArgSubterm subFn)
  appNeverSubOwnArg (ThereAppArg subArg) = appNeverSubOwnArg (appArgSubterm subArg)
  appNeverSubOwnArg (ThereAbsBody subBody) = absNeverSubOwnBody (appArgSubterm subBody)

  ||| An Abstraction cannot be a subterm of its own `body` because that would require
  ||| an infinitely nested lambda expression.
  public export
  absNeverSubOwnBody : Subterm (Abstraction param body) body -> Void
  absNeverSubOwnBody (Here Refl) impossible
  absNeverSubOwnBody (ThereAppFn subFn) = appNeverSubOwnFn (absBodySubterm subFn)
  absNeverSubOwnBody (ThereAppArg subArg) = appNeverSubOwnArg (absBodySubterm subArg)
  absNeverSubOwnBody (ThereAbsBody subBody) = absNeverSubOwnBody (absBodySubterm subBody)

||| If the terms in the subterm relation can be swapped around then they must be equal.
public export
subtermEqualWhenCommutative : Subterm a b -> Subterm b a -> a = b
subtermEqualWhenCommutative (Here Refl) bSubA = Refl
subtermEqualWhenCommutative (ThereAppFn subFn) bSubA =
  let (Refl) = subtermEqualWhenCommutative subFn (appFnSubterm bSubA)
  in absurd (appNeverSubOwnFn bSubA)  
subtermEqualWhenCommutative (ThereAppArg subArg) bSubA = 
  let (Refl) = subtermEqualWhenCommutative subArg (appArgSubterm bSubA)
  in absurd (appNeverSubOwnArg bSubA)
subtermEqualWhenCommutative (ThereAbsBody subBody) bSubA = 
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

