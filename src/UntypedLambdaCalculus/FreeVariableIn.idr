module UntypedLambdaCalculus.FreeVariableIn

import Decidable.Equality

import UntypedLambdaCalculus

data FreeIn: (name: String) -> Term -> Type where
  Here: FreeIn name (Variable name)
  ThereAppFn: (freeInFn: FreeIn name fn) -> FreeIn name (Application fn arg)
  ThereAppArg: (freeInArg: FreeIn name arg) -> FreeIn name (Application fn arg)
  ThereAbsBody: (notBinding: Not (name = param)) -> (freeInBody: FreeIn name body) -> FreeIn name (Abstraction param body) 

neverFreeInVarWhenNameNeq : FreeIn name1 (Variable name2) -> Not (name1 = name2) -> Void
neverFreeInVarWhenNameNeq Here nameNeq = nameNeq Refl 

neverFreeInBindingAbs : FreeIn name (Abstraction name body) -> Void
neverFreeInBindingAbs (ThereAbsBody notBinding freeInBody) = notBinding Refl

isFreeIn : (var: String) -> (term: Term) -> Dec (var `FreeIn` term)
isFreeIn var term =
  case term of
    Variable name => 
      case decEq var name of
        Yes Refl => 
          Yes Here

        No nameNeq => 
          No (\freeInTerm => neverFreeInVarWhenNameNeq freeInTerm nameNeq)
    
    Application fn arg => 
      case var `isFreeIn` fn of
        Yes freeInFn => 
          Yes (ThereAppFn freeInFn)

        No notFreeInFn => 
          case var `isFreeIn` arg of
            Yes freeInArg => 
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

