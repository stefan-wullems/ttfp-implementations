module UntypedLambdaCalculus.FreeIn

import Decidable.Equality

import UntypedLambdaCalculus

||| A path proof that a certain variable is a free in some lamba expression.
data FreeIn: (name: String) -> Term -> Type where
  Here: FreeIn name (Variable name)
  ThereAppFn: (freeInFn: FreeIn name fn) -> FreeIn name (Application fn arg)
  ThereAppArg: (freeInArg: FreeIn name arg) -> FreeIn name (Application fn arg)
  ThereAbsBody: (notBinding: Not (name = param)) -> (freeInBody: FreeIn name body) -> FreeIn name (Abstraction param body) 

||| A variable can never be free in a lambda expression that does not contain that variable.
neverFreeInVarWhenNameNeq : FreeIn name1 (Variable name2) -> Not (name1 = name2) -> Void
neverFreeInVarWhenNameNeq Here nameNeq = nameNeq Refl 

||| A variable can never be free in the body of an abstraction that binds that variable.
neverFreeInBindingAbs : FreeIn name (Abstraction name body) -> Void
neverFreeInBindingAbs (ThereAbsBody notBinding freeInBody) = notBinding Refl

||| Decide whether a variable is a free in a certain lambda expression.
isFreeIn : (var: String) -> (term: Term) -> Dec (var `FreeIn` term)
isFreeIn var term =
  case term of
    Variable name => 
      case decEq var name of
        Yes Refl => 
          -- A variable is obviously bound in a lambda expression containing only that variable.
          Yes Here

        No nameNeq =>
          -- A variable is obviously not bound in a lambda expression containing only another variable.
          No (\freeInTerm => neverFreeInVarWhenNameNeq freeInTerm nameNeq)
    
    Application fn arg =>
      case var `isFreeIn` fn of
        Yes freeInFn =>
          -- If a variable is free in the `fn` of an Abstraction, it is also free in the Abstraction itself.
          Yes (ThereAppFn freeInFn)

        No notFreeInFn => 
          case var `isFreeIn` arg of
            Yes freeInArg => 
              -- If a variable is free in the `arg` of an Abstraction, it is also free in the Abstraction itself.
              Yes (ThereAppArg freeInArg)

            No notFreeInArg => 
              No (\freeInApp => 
                case freeInApp of
                  ThereAppFn freeInFn => 
                    notFreeInFn freeInFn

                  ThereAppArg freeInArg => 
                    notFreeInArg freeInArg
              )

    Abstraction param body =>
      case decEq var param of
        Yes Refl =>
          No neverFreeInBindingAbs

        No absNotBinding => 
          case var `isFreeIn` body of
            Yes freeInBody => 
              Yes (ThereAbsBody absNotBinding freeInBody)

            No notFreeInBody => 
              No (\freeInAbs => 
                case freeInAbs of
                  ThereAbsBody notBinding freeInBody =>
                    notFreeInBody freeInBody 
              )


