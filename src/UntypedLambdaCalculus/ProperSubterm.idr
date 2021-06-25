module UntypedLambdaCalculus.ProperSubterm

import Decidable.Equality

import UntypedLambdaCalculus
import UntypedLambdaCalculus.Subterm

%default total

||| A proper subterm is equivalent to the subterm relation, excluding reflexivity. 
public export
data ProperSubterm : (subTerm, term: Term) -> Type where
  ThereAppFn: (subFn: Subterm subTerm fn) -> ProperSubterm subTerm (Application fn arg)
  ThereAppArg: (subArg: Subterm subTerm arg) -> ProperSubterm subTerm (Application fn arg)
  ThereAbsBody: (subBody: Subterm subTerm body) -> ProperSubterm subTerm (Abstraction param body)

||| A term cannot be a proper subterm of itself because that would require an infinitely nested lambda expression.
public export
properSubtermNeverReflexive : ProperSubterm term term -> Void
properSubtermNeverReflexive termPsubSelf = 
  case termPsubSelf of
    ThereAppFn appSubOwnFn =>
      appNeverSubOwnFn appSubOwnFn

    ThereAppArg appSubOwnArg =>
      appNeverSubOwnArg appSubOwnArg

    ThereAbsBody absSubOwnBody =>
      absNeverSubOwnBody absSubOwnBody

||| If `a` is a proper subterm of `b`, it is also a subterm of `b`.
toSubterm : ProperSubterm a b -> Subterm a b
toSubterm (ThereAppFn subFn) = ThereAppFn subFn
toSubterm (ThereAppArg subArg) = ThereAppArg subArg
toSubterm (ThereAbsBody subBody) = ThereAbsBody subBody

||| If `a` is a subterm of `b` and it is not equal to `b`, then it is a proper subterm.
fromSubterm : Subterm a b -> (aNeqB: Not (a = b)) -> ProperSubterm a b
fromSubterm Here aNeqB = absurd (aNeqB Refl)
fromSubterm (ThereAppFn subFn) aNeqB = ThereAppFn subFn
fromSubterm (ThereAppArg subArg) aNeqB = ThereAppArg subArg
fromSubterm (ThereAbsBody subBody) aNeqB = ThereAbsBody subBody

||| A proper subterm can never be commutative because that would imply that it is reflexive.
public export
properSubtermNeverCommutative : ProperSubterm a b -> ProperSubterm b a -> Void
properSubtermNeverCommutative aPsubB bPsubA = 
  let (Refl) = subtermEqualWhenCommutative (toSubterm aPsubB) (toSubterm bPsubA) 
  in properSubtermNeverReflexive aPsubB

||| Given a proof that `a` is a proper subterm of `b`, 
||| and a proof that `b` is a proper subterm of `c`,
||| derive a proof that `a` is also a proper subterm of `c`.
public export
properSubtermTransitivity : ProperSubterm a b -> ProperSubterm b c -> ProperSubterm a c
properSubtermTransitivity aPsubB bPsubC = 
  let aPsubC = subtermTransitivity (toSubterm aPsubB) (toSubterm bPsubC)
  in fromSubterm aPsubC (\Refl => properSubtermNeverCommutative aPsubB bPsubC)

||| If an `Application` is a proper subterm of some term, it's `fn`, is also a proper subterm of that term.
public export
appFnProperSubterm : ProperSubterm (Application fn arg) term -> ProperSubterm fn term
appFnProperSubterm prf = properSubtermTransitivity (ThereAppFn Here) prf

||| If an `Application` is a proper subterm of some term, it's `arg`, is also a proper subterm of that term.
public export 
appArgProperSubterm : ProperSubterm (Application fn arg) term -> ProperSubterm arg term
appArgProperSubterm prf = properSubtermTransitivity (ThereAppArg Here) prf

||| If an `Abstraction` is a proper subterm of some term, it's `body`, is also a proper subterm of that term.
public export
absBodyProperSubterm : ProperSubterm (Abstraction param body) term -> ProperSubterm body term
absBodyProperSubterm prf = properSubtermTransitivity (ThereAbsBody Here) prf

||| Decide whether a term is a proper subterm of another.
public export
isProperSubterm : (a, b: Term) -> Dec (ProperSubterm a b)
isProperSubterm a b =
  case isSubterm a b of
    Yes aSubB =>
      case aSubB of
        Here =>
          No properSubtermNeverReflexive

        ThereAppFn aSubFn => 
          Yes (ThereAppFn aSubFn) 

        ThereAppArg aSubArg => 
          Yes (ThereAppArg aSubArg)

        ThereAbsBody aSubBody => 
          Yes (ThereAbsBody aSubBody)

    No aNsubB =>
      -- If `a` is not a subterm of `b`, it is also not a proper subterm of `b`.
      No (\aPsubB => 
        case aPsubB of
          ThereAppFn aSubFn => 
            aNsubB (ThereAppFn aSubFn)

          ThereAppArg aSubArg => 
            aNsubB (ThereAppArg aSubArg)

          ThereAbsBody aSubBody => 
            aNsubB (ThereAbsBody aSubBody)
      )

public export
Uninhabited (ProperSubterm term term) where uninhabited = properSubtermNeverReflexive
