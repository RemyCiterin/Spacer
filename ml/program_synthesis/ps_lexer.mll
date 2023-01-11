
{
(* ce fichier est inpirer du TP minilustre *)
open Parser
open Lexing
open Ps_parser
exception Lexical_error of string
open Ps_ast

let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

let string_to_ident =
  begin
    let table = Hashtbl.create 42 in

    List.iter (fun (x, y) -> Hashtbl.replace table x y) [
      "primitive", PRIMITIVE; "if", IF; "then", THEN; "else", ELSE;
      "and", AND; "or", OR; "not", NOT; "let", LET; "in", IN;
      "example", EXAMPLE; "variables", VARIABLES; "bool", BOOL;
      "true", TRUE; "false", FALSE; "goal", GOAL; "xor", XOR;
    ];

    let aux name = match Hashtbl.find_opt table name with
    | None   -> IDENT name
    | Some i -> i
    in aux
  end
}

let ident = ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let integer = ("0x" ['0'-'9' 'a'-'f' 'A'-'F']+ ) | ("0b" ('0' | '1')+) | ['0'-'9']+


rule token = parse
    | (' ' | '\t')   {token lexbuf}

    | '\n'           {newline lexbuf; token lexbuf}
    | ":="           {DEF}
    | ":"            {HAS_TYPE}
    | ";"            {PV}
    | ","            {V}
    | "{"            {LEFT_B}
    | "}"            {RIGHT_B}

    | "("            {LEFT_P}
    | ")"            {RIGHT_P}

    | ident as i     {string_to_ident i}
    | integer as i   {INT (int_of_string i)}

    | "->"           {ARROW}

    | "=="           {EQ}

    | ("/\\" | "&&") {AND}
    | ("\\/" | "||") {OR}
    | ("~" | "!")    {NOT}
    | "^"            {XOR}

    | "."            {DOT}

    | eof            {EOF}

    | "//"           {comment lexbuf}

    | _              {raise (Lexical_error "unknow caracter")}

and comment = parse
    | '\n'          {newline lexbuf; token lexbuf}
    | _             {comment lexbuf}
    | eof           {EOF}
