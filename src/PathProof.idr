module PathProof

import Data.Vect
import Data.List.Elem

import Decidable.Equality

import UntypedLambdaCalculus

data SubtermPath : Term -> Term -> Type where
  AppFn: SubtermPath (Application fn arg) fn
  AppArg: SubtermPath (Application fn arg) arg
  AbsBody: SubtermPath (Abstraction param body) body

Uninhabited (SubtermPath (Variable name) term) where
  uninhabited prf impossible

testSubtermPaths : (term: Term) -> (len ** Vect len (term' ** SubtermPath term term'))  
testSubtermPaths term = 
  case term of
    Variable name => 
      (_ ** [])

    Application fn arg => 
      (_ ** [(_ ** AppFn), (_ ** AppArg)])

    Abstraction param body => 
      (_ ** [(_ ** AbsBody)])

data ListPath : List a -> List a -> Type where
  Tail: ListPath (x :: xs) xs 

namespace Any

  ||| A proof that some subterm of a term satisfies a certain property.
  |||
  ||| @ mkPath the type of the possible paths
  ||| @ p the property to be satisfied
  public export
  data Any : {0 pathType:_ } -> (next: (xs: as) -> List (xs': as ** pathType xs xs')) -> (p : as -> Type) -> as -> Type where
    ||| A proof that the satifsying term is the term we're currently examining.
    Here: {0 pathType: _} -> {0 next: (xs: as) -> List (xs': as ** pathType xs xs')} -> (prf: p xs) -> Any next p xs
    ||| A proof that the satisfying element is found somewhere later in the structure.
    There: {0 pathType: _} -> 
           {0 next: (xs:as) -> List (xs': as ** pathType xs xs')} -> 
           {0 p: as -> Type} -> 
           {xs, xs': _} ->
           (path: pathType xs xs') ->
           Elem (xs' ** path) (next xs) -> 
           (later: Any next p xs') -> 
           Any next p xs

  ||| Modify the property.
  export
  mapProperty : (f: forall x . p x -> q x) -> Any next p xs -> Any next q xs
  mapProperty f (Here prf) = Here (f prf)
  mapProperty f (There path inSubstructure later) = There path inSubstructure (mapProperty f later)
  
  any : {0 pathType: _} ->
        (next: (xs: as) -> List (xs': as ** pathType xs xs')) -> 
        (dec: (xs: as) -> Dec (p xs)) -> 
        (xs: as) -> 
        Dec (Any next p xs)
  any next dec xs = anyHelp xs
    where
      anyHelp : (xs: as) -> Dec (Any next p xs)
      anyHelp xs =
        case dec xs of
          Yes prf => 
            Yes (Here prf)

          No notHere =>
            case inSubstructure xs of
               Yes (xs' ** path ** (isSubterm, prf)) =>
                  Yes (There path isSubterm prf)

               No notInSubstructure => 
                 No (\prfSomewhere => 
                   case prfSomewhere of
                     Here prfHere => 
                       notHere prfHere

                     There path isSubterm prfInSubstructure => 
                       notInSubstructure (_ ** path ** (isSubterm, prfInSubstructure)) 
                 )

        where
          inSubstructure : (xs: as) -> Dec (xs': as ** path: pathType xs xs' ** (Elem (xs' ** path) (next xs), Any next p xs'))
          inSubstructure xs = inSubstructureHelp (next xs)
            where
              inSubstructureHelp : (subterms: List (xs': as ** pathType xs xs')) -> Dec (xs': as ** path: pathType xs xs' ** (Elem (xs' ** path) subterms, Any next p xs'))
              inSubstructureHelp [] = No (\(_ ** _ ** (prf, _)) => uninhabited prf)
              inSubstructureHelp ((xs' ** path) :: paths) = 
                case anyHelp xs' of
                  Yes prf => 
                    Yes (xs' ** path ** (Here, prf))

                  No notInSubstructureXs' => 
                    case inSubstructureHelp paths of
                      Yes (xs'' ** path' ** (isSubterm, prf)) => 
                        Yes (xs'' ** path' ** (There isSubterm, prf))

                      No notInSubstructureXs => 
                        No (\(xs''''' ** path ** (prfInBla, whattPrf)) => 
                         case prfInBla of
                           Here => notInSubstructureXs' whattPrf
                           There x => notInSubstructureXs (xs''''' ** path ** (x, whattPrf))
                        )
                                                                              
      
      
               
          

        
      
          

        
