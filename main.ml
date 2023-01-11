open Format

open Z3
open Z3.AST
open Z3.Symbol
open Z3.FuncDecl
open Z3.Params
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic
open Z3.Arithmetic.Real
open Z3.Arithmetic.Integer
open Z3.BitVector
open Z3.Solver

open CHC
open Utils
open Parse_horn

open Ast
open Ast_to_c
open Lexer
open Lexing
open Parsing
open Parser
open Ast_unfolded
open Solver_wrapper
open Spacer
open Ps_main
let input_file = "tests/test.brainfuck"


let get_loc lb = (lexeme_start_p lb, lexeme_end_p lb)
(*
let print_loc lb =
    let (start_pos, end_pos) = get_loc lb in
	let l_start = start_pos.pos_lnum in
    let l_end   = end_pos.pos_lnum   in
	let c_start = start_pos.pos_cnum - start_pos.pos_bol + 1 in
	let c_end   = end_pos.pos_cnum   - start_pos.pos_bol + 1 in
    if l_start = l_end then
	    Format.printf "File \"%s\", line %d, characters %d-%d:\n" input_file l_start c_start c_end
    else
        Format.printf "File \"%s\", line %d-%d:\n" input_file l_start l_end
*)

let cfg = [("model", "true"); ("proof", "true")]
let ctx = mk_context cfg


let _ =
  begin
    (*
        int x, y, n, m;
        x=y=0; n=m;
        assume (n >= 0);

    l1:  while (n > 0) {
            if (nondet()) x++;
            else y++;
            n--;
        }

    l4: assert (m == x + y);
    *)
    let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
    let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
    let one  = Z3.Arithmetic.Integer.mk_numeral_i ctx 1 in

    let x = fresh_variable ctx int_sort in
    let y = fresh_variable ctx int_sort in
    let n = fresh_variable ctx int_sort in
    let m = fresh_variable ctx int_sort in

    let x_ = fresh_variable ctx int_sort in
    let y_ = fresh_variable ctx int_sort in
    let n_ = fresh_variable ctx int_sort in
    let m_ = fresh_variable ctx int_sort in

    let l1 = Z3.FuncDecl.mk_fresh_func_decl ctx "l1" [
      int_sort; int_sort; int_sort; int_sort;
    ] (Z3.Boolean.mk_sort ctx) in

    let l2 = Z3.FuncDecl.mk_fresh_func_decl ctx "l2" [
      int_sort; int_sort; int_sort;
    ] (Z3.Boolean.mk_sort ctx) in

    let l3 = Z3.FuncDecl.mk_fresh_func_decl ctx "l2" [
      int_sort; int_sort;
    ] (Z3.Boolean.mk_sort ctx) in

    let l4 = Z3.FuncDecl.mk_fresh_func_decl ctx "l2" [
      int_sort;
    ] (Z3.Boolean.mk_sort ctx) in

    let rule1 = (
      None, [],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx x y;
        Boolean.mk_eq ctx n m;
        Boolean.mk_eq ctx x zero;
        Arithmetic.mk_ge ctx n zero
      ],
      mk_app ctx l1 [x; y; n; m]
    ) in

    let rule2 = (None,
      [mk_app ctx l1 [x; y; n; m]],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx m m_;
        Boolean.mk_eq ctx x x_;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [n_; one]) n;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [y ; one]) y_;
        Arithmetic.mk_gt ctx n zero
      ],
      mk_app ctx l1 [x_; y_; n_; m_]
    ) in

    let rule3 = (None,
      [mk_app ctx l1 [x; y; n; m]],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx m m_;
        Boolean.mk_eq ctx y y_;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [n_; one]) n;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [x ; one]) x_;
        Arithmetic.mk_gt ctx n zero
      ],
      mk_app ctx l1 [x_; y_; n_; m_]
    ) in

    let rule4 = (None,
      [mk_app ctx l1 [x; y; n; m]],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx m m_;
        Boolean.mk_eq ctx y y_;
        Boolean.mk_eq ctx x x_;
        Arithmetic.mk_le ctx n zero
      ],
      mk_app ctx l2 [x_; y_; m_]
    ) in

    let rule5 = (None,
      [mk_app ctx l2 [x; y; m]],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [m; one]) m_;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [x; one]) x_;
        Arithmetic.mk_gt ctx x zero;
        Boolean.mk_eq ctx y y_;
      ],
      mk_app ctx l2 [x_; y_; m_]
    ) in

    let rule6 = (None,
      [mk_app ctx l2 [x; y; m]],
      Boolean.mk_and ctx [
        Arithmetic.mk_le ctx x zero;
        Boolean.mk_eq ctx m m_;
        Boolean.mk_eq ctx x x_;
        Boolean.mk_eq ctx y y_;
      ],
      mk_app ctx l3 [y_; m_]
    ) in

    let rule7 = (None,
      [mk_app ctx l3 [y; m]],
      Boolean.mk_and ctx [
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [m; one]) m_;
        Boolean.mk_eq ctx (Arithmetic.mk_add ctx [y; one]) y_;
        Arithmetic.mk_gt ctx y zero;
      ],
      mk_app ctx l3 [y_; m_]
    ) in

    let rule8 = (None,
      [mk_app ctx l3 [y; m]],
      Boolean.mk_and ctx [
        Arithmetic.mk_le ctx y zero;
        Boolean.mk_eq ctx m m_;
      ],
      mk_app ctx l4 [m_]
    ) in

    let query = (None,
      [mk_app ctx l4 [m]],
      Boolean.mk_not ctx (Boolean.mk_eq ctx m zero)
    ) in

    let chc_list = [
      CHCRule rule1; CHCRule rule2; CHCRule rule3;
      CHCRule rule4; CHCRule rule5; CHCRule rule6;
      CHCRule rule7; CHCRule rule8; CHCQuery query
    ] in

    let chc_solver = initial_chc_solver ctx chc_list in

    (*
    for i=0 to 10 do
      let b = bounded_model_checking chc_solver i in
      Format.printf "\r%d: %b" i b; Format.print_flush ();
    done; Format.printf "\n";
    *)

    Format.printf "%b\n" (Option.is_none (Spacer.model_checking chc_solver));
    Format.print_flush ();

    ()

  end

let _ = begin
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in

  let x = fresh_variable ctx int_sort in
  let r = fresh_variable ctx int_sort in
  let z = fresh_variable ctx int_sort in
  let y = fresh_variable ctx int_sort in

  let mc = Z3.FuncDecl.mk_fresh_func_decl ctx "mc" [
    int_sort; int_sort;
  ] (Z3.Boolean.mk_sort ctx) in

  let rule1 = (
    None, [],
    Boolean.mk_and ctx [
      Arithmetic.mk_gt ctx x (Integer.mk_numeral_i ctx 100);
      Boolean.mk_eq ctx x (Arithmetic.mk_add ctx [r; Integer.mk_numeral_i ctx 10])
    ],
    mk_app ctx mc [x; r]
  ) in

  let rule2 = (None,
    [mk_app ctx mc [y; z]; mk_app ctx mc [z; r]],
    Boolean.mk_and ctx [
      Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; Integer.mk_numeral_i ctx 11]);
      Arithmetic.mk_le ctx x (Integer.mk_numeral_i ctx 100)
    ],
    mk_app ctx mc [x; r]
  ) in

  let query = (None,
    [mk_app ctx mc [x; r]],
    Boolean.mk_and ctx [
      Arithmetic.mk_le ctx x (Integer.mk_numeral_i ctx 101);
      Boolean.mk_not ctx (Boolean.mk_eq ctx r (Integer.mk_numeral_i ctx 91))
    ]
  ) in

  let chc_solver = initial_chc_solver ctx [CHCRule rule1; CHCRule rule2; CHCQuery query] in

  Format.printf "SPACER: %b\n" (Option.is_none (Spacer.model_checking chc_solver)); Format.print_flush ();
  Format.print_flush ();

  print_chc_smt2 ctx [CHCRule rule1; CHCRule rule2; CHCQuery query];
  ()

end

let _ =
    let c = open_in input_file in
    let lb = Lexing.from_channel c in

    try
        let file = Parser.file Lexer.token lb in

        let file = convert file in
        let chc_list = to_chc native_chc_generation_config file ctx in


        (*
        let chc_list = Ast_to_chc.construct_chc file ctx Ast_to_chc.native_chc_generation_config in
        *)

        print_chc_smt2 ctx chc_list;

        let chc_solver = initial_chc_solver ctx chc_list in

        (*for i=0 to 100 do
            let b = bounded_model_checking chc_solver i in
            Format.printf "\r%d: %b" i b; Format.print_flush ();
        done;Format.printf "\n";*)

        Format.printf "%b\n" (Option.is_some (Spacer.model_checking chc_solver));

        Format.print_flush ();


        (* ast_to_c file; *)
        close_in c;
        ()
    with
		| Lexer.Lexical_error s ->
			begin
				(*print_loc lb;*)
				Format.printf "%s\n" s;
			end

		| Parsing.Parse_error ->
			begin
				(*print_loc lb;*)
				Format.printf "Syntax error\n";
			end

