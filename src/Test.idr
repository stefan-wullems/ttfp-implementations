export
  interface Iterable iterable where
    constructor MkIterable
    curr : iterable a -> a
    next : {pathType: iterable a -> iterable a -> Type} -> (xs: iterable a) -> List (xs': iterable a ** pathType xs xs')

