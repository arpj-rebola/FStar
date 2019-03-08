module ListStuff

type alist (#a : Type) =
    | ANil : alist #a
    | ACons : (head : a) -> (tail : alist #a) -> alist #a
