
%{
open Ps_ast
open Lexing
open Parsing

let loc () = symbol_start_pos (), symbol_end_pos ()
%}

%token PRIMITIVE
%token IF
%token THEN
%token ELSE
%token AND
%token OR
%token EQ
%token NOT
%token LET
%token IN
%token TRUE
%token FALSE
%token EXAMPLE
%token VARIABLES
%token RIGHT_B
%token RIGHT_P
%token HAS_TYPE
%token LEFT_B
%token LEFT_P
%token DEF
%token BOOL
%token PV
%token ARROW
%token DOT
%token <int> INT
%token <string> IDENT
%token EOF
%token GOAL
%token V
%token XOR


%left PV
%nonassoc IN
%nonassoc ELSE
%left OR
%left AND XOR
%left EQ
%nonassoc NOT

%start file
%type <Ps_ast.dsl> file

%%

file:
    | VARIABLES variables HAS_TYPE ty primitives exemples EOF {($2, $4, $5 $2, $6 $2 $4, None)}
    | VARIABLES variables HAS_TYPE ty primitives exemples GOAL expr EOF {($2, $4, $5 $2, $6 $2 $4, Some ($8 $2))}
variables:
  | {SMap.empty}
  | LEFT_P IDENT HAS_TYPE ty RIGHT_P variables {

    if SMap.mem $2 $6 then
      raise (Typing_error ("the variable `" ^ $2 ^ "`already exist", loc ()));

    SMap.add $2 $4 $6
  }

const:
  | TRUE  {CBool true}
  | FALSE {CBool false}
  | LEFT_B const_named_tuple RIGHT_B {CNamedTuple $2}
  | LEFT_P const_named_tuple2 RIGHT_P {CNamedTuple $2}

const_named_tuple2:
  | const V {SMap.singleton "0" $1}
  | const_named_tuple2 const V {SMap.add (string_of_int (SMap.cardinal $1)) $2 $1}

const_named_tuple:
  | {SMap.empty}
  | IDENT DEF const {SMap.singleton $1 $3}
  | INT   DEF const {SMap.singleton (string_of_int $1) $3}
  | const_named_tuple PV const_named_tuple {SMap.union (fun n _ _ -> raise (Typing_error ("this named-tuple have two times the field `" ^ n ^ "`", loc ()))) $1 $3}

ty:
  | BOOL {TBool}
  | LEFT_B ty_content RIGHT_B {TNamedTuple $2}
  | LEFT_P ty_content2 RIGHT_P {TNamedTuple $2}

ty_content2:
  | ty V {SMap.singleton "0" $1}
  | ty_content2 ty V {SMap.add (string_of_int (SMap.cardinal $1)) $2 $1}

ty_content:
  | IDENT HAS_TYPE ty {SMap.singleton $1 $3}
  | INT   HAS_TYPE ty {SMap.singleton (string_of_int $1) $3}
  | ty_content PV ty_content {SMap.union (fun n _ _ -> raise (Typing_error ("this named-tuple have two times the field `" ^ n ^ "`", loc ()))) $1 $3}
  | {SMap.empty}

primitives:
  | {fun env -> SMap.empty}
  | PRIMITIVE IDENT variables HAS_TYPE ty DEF expr primitives {
    fun env ->
      let q = $8 env in
      if SMap.mem $2 q then
        raise (Typing_error ("the primitive `" ^ $2 ^ "` already exists", loc ()));
      if SMap.mem $2 env then
        raise (Typing_error ("the primitive `" ^ $2 ^ "` is also the name of a variable", loc ()));
      SMap.add $2 (Primitive ($5, $3, $7 (SMap.fold SMap.add $3 env))) q
  }

exemples:
  | {fun env out -> []}
  | EXAMPLE const ARROW const exemples {
    fun env out ->
      if not (equal_type (ty_of_const $2) (TNamedTuple env)) then raise (Typing_error ("`" ^ ty_to_string (ty_of_const $2) ^ "` is different to `" ^ ty_to_string (TNamedTuple env) ^ "`", loc ()));
      if not (equal_type (ty_of_const $4) out) then raise (Typing_error ("`" ^ ty_to_string (ty_of_const $4) ^ "` is different to `" ^ ty_to_string out ^ "`", loc ()));
      ($2, $4) :: $5 env out
  }

expr:
  | expr XOR expr              {let pos = loc () in fun env -> construct_expr pos env (Binop ($1, Xor, $3))}
  | expr AND expr              {let pos = loc () in fun env -> construct_expr pos env (Binop ($1, And, $3))}
  | expr OR  expr              {let pos = loc () in fun env -> construct_expr pos env (Binop ($1, Or , $3))}
  | expr EQ  expr              {let pos = loc () in fun env -> construct_expr pos env (Binop ($1, Eq , $3))}
  | NOT expr                   {let pos = loc () in fun env -> construct_expr pos env (Unop (Not, $2))}
  | LET IDENT DEF expr IN expr {let pos = loc () in fun env -> construct_expr pos env (LetIn ($2, $4, $6))}
  | TRUE                       {let pos = loc () in fun env -> construct_expr pos env (Const true)}
  | FALSE                      {let pos = loc () in fun env -> construct_expr pos env (Const false)}
  | IF expr THEN expr ELSE expr{let pos = loc () in fun env -> construct_expr pos env (ITE ($2, $4, $6))}
  | LEFT_B named_tuple RIGHT_B {let pos = loc () in fun env -> construct_expr pos env (NamedTuple $2)}
  | LEFT_P named_tuple2 RIGHT_P{let pos = loc () in fun env -> construct_expr pos env (NamedTuple $2)}
  | dot_expression             {$1}

dot_expression:
  | dot_expression DOT IDENT {let pos = loc () in fun env -> construct_expr pos env (Unop (Get $3, $1))}
  | dot_expression DOT INT   {let pos = loc () in fun env -> construct_expr pos env (Unop (Get (string_of_int $3), $1))}
  | IDENT                    {let pos = loc () in fun env -> construct_expr pos env (Variable $1)}
  | LEFT_P expr RIGHT_P      {$2}

named_tuple:
  | {SMap.empty}
  | INT   DEF expr {SMap.singleton (string_of_int $1) $3}
  | IDENT DEF expr {SMap.singleton $1 $3}
  | named_tuple PV named_tuple {SMap.union (fun n _ _ -> raise (Typing_error ("this named-tuple have two times the field `" ^ n ^ "`", loc ()))) $1 $3}

named_tuple2:
  | expr V {SMap.singleton "0" $1}
  | named_tuple2 expr V {SMap.add (string_of_int (SMap.cardinal $1)) $2 $1}
