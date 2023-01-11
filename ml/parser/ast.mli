type position = Lexing.position * Lexing.position 

type loc_expr = {loc: position; expr: expr}

and expr =
    | While of loc_expr list
    | Error
    | Write
    | Read
    | Incr
    | Decr
    | Left
    | Right