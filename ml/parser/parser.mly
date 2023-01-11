%{
open Ast 
open Lexing 
open Parsing

let loc () = symbol_start_pos (), symbol_end_pos ()
%}

%token ERROR
%token INCR
%token DECR 
%token WRITE
%token READ
%token LEFT
%token RIGHT
%token BEGIN
%token END
%token EOF

%start file
%type <Ast.loc_expr list> file

%%

file:
    | ast EOF {$1}

ast:
    | local_op ast {$1 :: $2}
    |               {[]}
;

local_op:
    | INCR {{loc= loc (); expr= Incr}}
    | DECR {{loc= loc (); expr= Decr}}
    | LEFT {{loc= loc (); expr= Left}}
    | RIGHT {{loc= loc (); expr= Right}}
    | READ {{loc= loc (); expr= Read}}
    | WRITE {{loc= loc (); expr= Write}}
    | ERROR {{loc= loc (); expr= Error}}
    | BEGIN ast END {{loc= loc (); expr= While $2}}
;