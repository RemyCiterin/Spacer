(** transform an Ast into a list of constrained Horn clauses *)

open CHC
open Utils

open Z3
open Z3.AST
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

(** configuration of the CHCs generalization *)
type chc_generation_config = {
    check_bounds: bool; (** if true: check that ptr is positive *)
    check_error_location: bool (** if true: check that the # caractere are unrecheables *)
}

let native_chc_generation_config = {
    check_bounds = true;
    check_error_location = true
}

(**
construct the variables of the CHCs system:
    - an integer: the pointer
    - an array from integer to bit-vector of size 8: the memory
return i, a, i', a'
*)
let get_variables ctx : formula * formula * formula * formula =
    begin
        let prev_ptr = fresh_variable ctx (Integer.mk_sort ctx) in
        let next_ptr = fresh_variable ctx (Integer.mk_sort ctx) in

        let prev_array = fresh_variable ctx (
            Z3.Z3Array.mk_sort ctx (Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
        ) in

        let next_array = fresh_variable ctx (
            Z3.Z3Array.mk_sort ctx (Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
        ) in

        (prev_ptr, prev_array, next_ptr, next_array)
    end

(** return the sorts of the variables of a brainfuck program *)
let get_variables_sorts ctx = [
        Integer.mk_sort ctx;
        Z3.Z3Array.mk_sort ctx (Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
    ]

(**
a labeled expression is an expression labled byone predicate
*)
type labeled_expr =
    | While of labeled_expr list * predicate
    | Error of predicate
    | Write of predicate
    | Read  of predicate
    | Incr  of predicate
    | Decr  of predicate
    | Left  of predicate
    | Right of predicate

(** transform an ast into a labeled ast *)
let rec add_labels ctx (ast:Ast.loc_expr) : labeled_expr =
    let sorts = get_variables_sorts ctx in

    let rec aux (ast:Ast.loc_expr) =
        let label = fresh_predicate ctx sorts in

        match ast.expr with
        | Ast.While ast -> While (List.map aux ast, label)
        | Ast.Error     -> Error label
        | Ast.Write     -> Write label
        | Ast.Read      -> Read  label
        | Ast.Incr      -> Incr  label
        | Ast.Decr      -> Decr  label
        | Ast.Left      -> Left  label
        | Ast.Right     -> Right label
    in

    aux ast


(** given a partial program (a list of labeled expressions), return the input label *)
let get_input_label (ast:labeled_expr list) : predicate option =
    match ast with
    | While (_, l) :: _ -> Some l
    | Error l      :: _ -> Some l
    | Write l      :: _ -> Some l
    | Read  l      :: _ -> Some l
    | Incr  l      :: _ -> Some l
    | Decr  l      :: _ -> Some l
    | Left  l      :: _ -> Some l
    | Right l      :: _ -> Some l
    | _ -> None

(** given a partial program, return the output label *)
let rec get_output_label (ast: labeled_expr list) : predicate option =
    match ast with
    | While (_, l) :: [] -> Some l
    | Error l      :: [] -> Some l
    | Write l      :: [] -> Some l
    | Read  l      :: [] -> Some l
    | Incr  l      :: [] -> Some l
    | Decr  l      :: [] -> Some l
    | Left  l      :: [] -> Some l
    | Right l      :: [] -> Some l
    | _ :: xs -> get_output_label xs
    | [] -> None

(**
return the set of CHCs associated to a program
*)
let construct_chc (ast: Ast.loc_expr list) ctx (config:chc_generation_config) : chc list =
    begin
        let (ptr_prev, array_prev, ptr_next, array_next) = get_variables ctx in

        let labeled_ast : labeled_expr list = List.map (add_labels ctx) ast in

        (* get the next predicate, and return the associatde list of constrained Horn clauses *)
        let rec aux (ast: labeled_expr) (next: predicate option) : chc list =
            match ast with
            | While (body, label) ->
                begin
                    let chc_list    = aux_list body (Some label) in

                    let first_label = match get_input_label body with
                        | None   -> label
                        | Some l -> l
                    in

                    let phi = mk_eq ctx
                        (BitVector.mk_numeral ctx "0" 8)
                        (Z3Array.mk_select ctx array_prev ptr_prev)
                    in
                    let mk_not ctx f = Boolean.mk_not ctx f in


                    CHCRule (
                        None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_not ctx phi,
                        mk_app ctx first_label [ptr_prev; array_prev]
                    ) :: match next with
                    | Some next -> CHCRule (
                        None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        phi,
                        mk_app ctx next [ptr_prev; array_prev]
                    ) :: chc_list
                    | None -> chc_list
                end
            | Error label ->
                begin
                    let error =
                        CHCQuery (
                            None,
                            [mk_app ctx label [ptr_prev; array_prev]],
                            mk_true ctx
                        )
                    in

                    let transition = match next with
                        | Some next -> [CHCRule (None,
                            [mk_app ctx label [ptr_prev; array_prev]],
                            mk_true ctx,
                            mk_app ctx next [ptr_prev; array_prev]
                        )]
                        | None -> []
                    in

                    if config.check_error_location then error :: transition else transition
                end
            | Write label ->
                begin
                    match next with
                    | Some next -> [CHCRule (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_true ctx,
                        mk_app ctx next [ptr_prev; array_prev]
                    )]
                    | None -> []
                end
            | Read label ->
                begin
                    match next with
                    | Some next -> [CHCRule (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_eq ctx array_next (
                            Z3Array.mk_store ctx array_prev ptr_prev (
                                fresh_variable ctx (BitVector.mk_sort ctx 8)
                            )
                        ),
                        mk_app ctx next [ptr_prev; array_next]
                    )]
                    | None -> []
                end
            | Incr label ->
                begin
                    match next with
                    | Some next -> [CHCRule (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_eq ctx array_next (
                            Z3Array.mk_store ctx array_prev ptr_prev (
                                BitVector.mk_add ctx
                                    (Z3Array.mk_select ctx array_prev ptr_prev)
                                    (BitVector.mk_numeral ctx "1" 8)
                            )
                        ),
                        mk_app ctx next [ptr_prev; array_next]
                    )]
                    | None -> []
                end
            | Decr label ->
                begin
                    match next with
                    | Some next -> [CHCRule (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_eq ctx array_next (
                            Z3Array.mk_store ctx array_prev ptr_prev (
                                BitVector.mk_sub ctx
                                    (Z3Array.mk_select ctx array_prev ptr_prev)
                                    (BitVector.mk_numeral ctx "1" 8)
                            )
                        ),
                        mk_app ctx next [ptr_prev; array_next]
                    )]
                    | None -> []
                end
            | Left label ->
                begin
                    let transition = match next with
                    | Some next -> [CHCRule (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_eq ctx ptr_next (
                            Arithmetic.mk_sub ctx [ptr_prev; Integer.mk_numeral_i ctx 1]
                        ),
                        mk_app ctx next [ptr_next; array_prev]
                    )]
                    | None -> []
                    in

                    let query = CHCQuery (None,
                        [mk_app ctx label [ptr_prev; array_prev]],
                        mk_eq ctx ptr_prev (Integer.mk_numeral_i ctx 0)
                    ) in

                    if config.check_bounds then query :: transition else transition
                end
                | Right label ->
                    begin
                        match next with
                        | Some next -> [CHCRule (None,
                            [mk_app ctx label [ptr_prev; array_prev]],
                            mk_eq ctx ptr_next (
                                Arithmetic.mk_add ctx [ptr_prev; Integer.mk_numeral_i ctx 1]
                            ),
                            mk_app ctx next [ptr_next; array_prev]
                        )]
                        | None -> []
                    end

        and aux_list (ast: labeled_expr list) (next: predicate option) : chc list =
            match ast with
            | t :: q ->
                begin
                    match get_input_label q with
                    | Some l -> aux t (Some l) @ aux_list q next
                    | None ->   aux t next
                end
            | [] -> []
        in

        match get_input_label labeled_ast with
        | Some p -> CHCRule (None, [], Boolean.mk_and ctx [
            mk_eq ctx (Integer.mk_numeral_i ctx 0) ptr_prev
        ;
            mk_eq ctx (Z3Array.mk_const_array ctx (Integer.mk_sort ctx) (BitVector.mk_numeral ctx "0" 8)) array_prev
        ], mk_app ctx p [ptr_prev; array_prev]) :: aux_list labeled_ast None
        | None -> aux_list labeled_ast None


    end

