module PathProof

import Data.Vect
import Data.List.Elem

import Decidable.Equality

namespace Any

  ||| A proof that some subterm of a term satisfies a certain property.
  |||
  ||| @ next Return all possible paths for a given structure
  ||| @ p The property to be satisfied
  public export
  data Any : {pathType:_ } -> (next: (xs: as) -> List (xs': as ** pathType xs xs')) -> (p : as -> Type) -> as -> Type where
    ||| A proof that the satifsying term is the term we're currently examining.
    Here: {pathType: _} -> {0 next: (xs: as) -> List (xs': as ** pathType xs xs')} -> (prf: p xs) -> Any next p xs
    ||| A proof that the satisfying element is found somewhere later in the structure.
    There: {pathType: _} -> 
           {0 next: (xs:as) -> List (xs': as ** pathType xs xs')} -> 
           {0 p: as -> Type} -> 
           {xs, xs': _} ->
           (path: pathType xs xs') ->
           {prfValidPath: Elem (xs' ** path) (next xs)} -> 
           (later: Any next p xs') -> 
           Any next p xs

  ||| Modify the property.
  export
  mapProperty : {pathType: _} -> 
                {next: (xs: as) -> List (xs': as ** pathType xs xs')} -> 
                (f: forall x . p x -> q x) -> 
                Any next p xs -> 
                Any next q xs
  mapProperty f (Here prf) = Here (f prf)
  mapProperty f (There path {prfValidPath} later) = There path {prfValidPath} (mapProperty f later) 

  ||| Decide if a certain property holds for any of the substructures of `xs`.
  |||
  ||| @next Traversal function
  ||| @dec Decide if a property holds for a structure
  ||| @xs Parent structure
  export
  any : {pathType: _} ->
           (next: (xs: as) -> List (xs': as ** pathType xs xs')) -> 
           (dec: (xs: as) -> Dec (p xs)) -> 
           (xs: as) -> 
           Dec (Any next p xs)
  any next dec xs = existsHelp xs
    where mutual
      existsHelp : (xs: as) -> Dec (Any next p xs)
      existsHelp xs =
        case dec xs of
          -- The property holds for `xs`.
          Yes prfProp => 
            Yes (Here prfProp)

          No contraProp =>
            -- The propety does not hold for `xs`. 
            -- Decide if it holds for any of the substructures of `xs`.
            case decExistsInSubstructure xs of
               -- The property is found to hold for one of the substructures of `xs`.
               Yes (xs' ** path ** (prfValidPath, existsInSubstructurePrf)) =>
                 Yes (There path {prfValidPath} existsInSubstructurePrf)

               -- The property does not hold for any of the substructures of `xs`.
               No contraExistsInSubstructure =>   
                 No (\existsPrf => 
                   case existsPrf of
                     Here prfProp => 
                       contraProp prfProp

                     There path {prfValidPath} existsInSubstructurePrf => 
                       contraExistsInSubstructure (_ ** path ** (prfValidPath, existsInSubstructurePrf)) 
                 )

      decExistsInSubstructure : (xs: as) -> Dec (xs': as ** path: pathType xs xs' ** (Elem (xs' ** path) (next xs), Any next p xs'))
      decExistsInSubstructure xs = decExistsInSubstructureHelp (next xs)
        where
          decExistsInSubstructureHelp : (subpaths: List (xs': as ** pathType xs xs')) -> 
                                        Dec (xs': as ** path: pathType xs xs' ** (Elem (xs' ** path) subpaths, Any next p xs'))
          decExistsInSubstructureHelp [] = No (\(_ ** _ ** (elemOfNextPrf, _)) => uninhabited elemOfNextPrf)
          decExistsInSubstructureHelp ((xs' ** path) :: paths) = 
            case existsHelp xs' of
              -- The property holds for this substructure.
              Yes prfExistsInThisSubstructure => 
                Yes (xs' ** path ** (Here, prfExistsInThisSubstructure))

              -- The property does not hold for this particular substructure.
              -- Decide if it holds for any of the other substructures of `xs`.
              No contraExistsInThisSubstructure =>
                case decExistsInSubstructureHelp paths of
                  -- The property holds for another substructure of `xs`.
                  Yes (xs'' ** path' ** (prfValidPath, prfExistsInAnotherSubstructure)) => 
                    Yes (xs'' ** path' ** (There prfValidPath, prfExistsInAnotherSubstructure))

                  -- The property does not hold for any of the substructures of `xs`.
                  No contraExistsInAnotherSubstructure => 
                    No (\(xs'' ** path ** (prfValidPath, prfExistsInSubstructure)) => 
                     case prfValidPath of
                       Here => 
                         contraExistsInThisSubstructure prfExistsInSubstructure

                       There prfLaterInSubstructure => 
                         contraExistsInAnotherSubstructure (xs'' ** path ** (prfLaterInSubstructure, prfExistsInSubstructure))
                    )

      

        
          
                                                                              
      
      
               
          

        
      
          

        
