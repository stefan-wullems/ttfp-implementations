module UntypedLambdaCalculus.Quantifiers

import UntypedLambdaCalculus

import PathProof

data SubtermPath : Term -> Term -> Type where 
  AppFn: SubtermPath (Application fn arg) fn 
  AppArg: SubtermPath (Application fn arg) arg 
  AbsBody: SubtermPath (Abstraction param body) body 

namespace Any

  ||| A proof that some subterm of a term satisfies a certain property.
  |||
  ||| @ p the property to be satisfied
  public export
  data Any : (p : Term -> Type) -> Term -> Type where
    ||| A proof that the satifsying term is the term we're currently examining.
    Here: (prf: p term) -> Any p term
    ||| A proof that the satisfying term is found somewhere under the `fn` of the `Application`. 
    ThereAppFn: (pSubFn: Any p fn) -> Any p (Application fn arg)
    ||| A proof that the satisfying term is found somewhere under the `arg` of the `Application`.
    ThereAppArg: (pSubArg: Any p arg) -> Any p (Application fn arg)
    ||| A proof that the satisfying term is found somewhere under the `body` of the `Abstraction`.
    ThereAbsBody: (pSubBody: Any p body) -> Any p (Abstraction param body)

  ||| Modify the property.
  export
  mapProperty : (f: {0 term : Term} -> p term -> q term) -> Any p t -> Any q t
  mapProperty f (Here prf) = Here (f prf)
  mapProperty f (ThereAppFn pSubFn) = ThereAppFn (mapProperty f pSubFn) 
  mapProperty f (ThereAppArg pSubArg) = ThereAppArg (mapProperty f pSubArg)
  mapProperty f (ThereAbsBody pSubBody) = ThereAbsBody (mapProperty f pSubBody)

  ||| If a certain property holds for one of the subterms of a variable,
  ||| then, because a variable only has itself as a subterm, we know that it holds for the variable.
  pSubtermVarImpliesPVar : Any p (Variable name) -> p (Variable name)
  pSubtermVarImpliesPVar (Here prf) = prf 

  ||| Given a decision procedure for a property, determine if a subterm of t satisfies it.
  |||
  ||| @ p the property to be satisfied
  ||| @ dec the decision procedure
  ||| @ term the term to examine
  export
  any : (dec : (subterm : Term) -> Dec (p subterm)) -> (term: Term) -> Dec (Any p term)  
  any dec term =
    case dec term of
      Yes pTerm => 
        Yes (Here pTerm)

      No notPTerm =>
        case term of
          Variable name => 
            No (\pSubVar => notPTerm (pSubtermVarImpliesPVar pSubVar))

          Application fn arg => 
            case any dec fn of
              Yes pSubFn => 
                Yes (ThereAppFn pSubFn)

              No pNsubFn => 
                case any dec arg of
                  Yes pSubArg => 
                    Yes (ThereAppArg pSubArg)

                  No pNsubArg => 
                    No (\pSubApp =>
                      case pSubApp of
                        Here pTerm => 
                          notPTerm pTerm

                        ThereAppFn pSubFn => 
                          pNsubFn pSubFn

                        ThereAppArg pSubArg => 
                          pNsubArg pSubArg
                    )

          Abstraction param body => 
            case any dec body of
              Yes pSubBody => 
                Yes (ThereAbsBody pSubBody)

              No pNsubBody => 
                No (\pSubAbs =>
                  case pSubAbs of
                    Here pTerm => 
                      notPTerm pTerm

                    ThereAbsBody pSubBody =>
                      pNsubBody pSubBody
                )
