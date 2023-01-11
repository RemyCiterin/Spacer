{
(* ce fichier est inpirer du TP minilustre *)
open Parser 
open Lexing

exception Lexical_error of string


let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

}

rule token = parse 
    | (' ' | '\t')  {token lexbuf}

    | '\n'          {newline lexbuf; token lexbuf}

    | '>'           {RIGHT}
    | '<'           {LEFT}
    | '+'           {INCR}
    | '-'           {DECR}
    | '.'           {WRITE}
    | ','           {READ}
    | '['           {BEGIN}
    | ']'           {END}
    | '#'           {ERROR}

    | eof           {EOF}

    | "//"          {comment lexbuf}

    | _             {raise (Lexical_error "unknow caracter")}

and comment = parse
    | '\n'          {newline lexbuf; token lexbuf}
    | _             {comment lexbuf}
    | eof           {EOF}
