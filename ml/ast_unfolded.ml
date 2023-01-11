open CHC
open Utils

module IntMap = Map.Make (struct
    type t = int
    let compare = compare
end)
module IntSet = Set.Make (struct
type t = int
let compare = compare
end)

(** return the sorts of the variables of a brainfuck program *)
let get_variables_sorts ctx = [
    Z3.Arithmetic.Integer.mk_sort ctx;
    Z3.Z3Array.mk_sort ctx (Z3.Arithmetic.Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
]

(** we assume that an expression doesn't have two consecutive blocks *)
type expr =
    | Error                                  (** error location *)
    | While of expr list                     (** while loop *)
    | Block of int * (int IntMap.t) * IntSet.t
        (** block of non-while expressions : new_ptr, min_ptr, det_updates, nondet_updates *)

type labeled_expr =
    | LError of predicate
    | LWhile of labeled_expr list * predicate
    | LBlock of int * (int IntMap.t) * IntSet.t * predicate

let rec label_ast ctx = function
    | Error :: q -> [LError (fresh_predicate ctx (get_variables_sorts ctx))]
    | Block (ptr_delta, det_updates, nondet_updates) :: q ->
        LBlock (ptr_delta, det_updates, nondet_updates, fresh_predicate ctx (get_variables_sorts ctx)) :: label_ast ctx q
    | While expr_list :: q->
        LWhile (label_ast ctx expr_list, fresh_predicate ctx (get_variables_sorts ctx)) :: label_ast ctx q
    | [] -> []

let get_input_label = function
    | LBlock (_, _, _, l) :: _ -> Some l
    | LWhile (_, l) :: _ -> Some l
    | LError l :: _ -> Some l
    | _ -> None


(** configuration of the CHC's convertion *)
type chc_generation_config = {
    min_addr: int option;
    max_addr: int option;
    check_error_loc: bool
}


let native_chc_generation_config = {
    check_error_loc = true;
    max_addr = None;
    min_addr = Some 0;
}

let get_variables ctx : formula * formula * formula * formula =
    begin
        let prev_ptr = fresh_variable ctx (Z3.Arithmetic.Integer.mk_sort ctx) in
        let next_ptr = fresh_variable ctx (Z3.Arithmetic.Integer.mk_sort ctx) in

        let prev_array = fresh_variable ctx (
            Z3.Z3Array.mk_sort ctx (Z3.Arithmetic.Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
        ) in

        let next_array = fresh_variable ctx (
            Z3.Z3Array.mk_sort ctx (Z3.Arithmetic.Integer.mk_sort ctx) (Z3.BitVector.mk_sort ctx 8)
        ) in

        (prev_ptr, prev_array, next_ptr, next_array)
    end

let rec to_chc config (ast: expr list) ctx : chc list =
    let prev_ptr, prev_array, next_ptr, next_array = get_variables ctx in

    let ast = label_ast ctx ast in

    let rec aux (ast : labeled_expr) (next:predicate option) : chc list =
        match ast with
        | LBlock (ptr_delta, det_updates, nondet_updates, pred) -> begin

            let min_index = match IntMap.min_binding_opt det_updates, IntSet.min_elt_opt nondet_updates with
                | Some (m, _), Some m' -> Some (min m m')
                | Some (m, _), _ -> Some m
                | _, Some m -> Some m
                | _ -> None
            in

            let max_index = match IntMap.max_binding_opt det_updates, IntSet.max_elt_opt nondet_updates with
                | Some (m, _), Some m' -> Some (max m m')
                | Some (m, _), _ -> Some m
                | _, Some m -> Some m
                | _ -> None
            in

            let queries_min = match min_index, config.min_addr with
                | Some m, Some m' -> [CHCQuery (None,
                    [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]],
                    Z3.Arithmetic.mk_lt ctx (Z3.Arithmetic.mk_add ctx [Z3.Arithmetic.Integer.mk_numeral_i ctx m; prev_ptr]) (Z3.Arithmetic.Integer.mk_numeral_i ctx m')
                )]
                | _ -> []
            in

            let queries_max = match max_index, config.max_addr with
                | Some m, Some m' -> [CHCQuery (None,
                    [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]],
                    Z3.Arithmetic.mk_gt ctx (Z3.Arithmetic.mk_add ctx [Z3.Arithmetic.Integer.mk_numeral_i ctx m; prev_ptr]) (Z3.Arithmetic.Integer.mk_numeral_i ctx m')
                )]
                | _ -> []
            in

            let array = IntSet.fold (
                fun i array ->
                    let index = Z3.Arithmetic.mk_add ctx [Z3.Arithmetic.Integer.mk_numeral_i ctx i; prev_ptr] in
                    let value = fresh_variable ctx (Z3.BitVector.mk_sort ctx 8) in
                    Z3.Z3Array.mk_store ctx array index value
            ) nondet_updates prev_array in

            let array = IntMap.fold (
                fun i j array ->
                    let index = Z3.Arithmetic.mk_add ctx [Z3.Arithmetic.Integer.mk_numeral_i ctx i; prev_ptr] in
                    let value = Z3.BitVector.mk_add ctx (Z3.BitVector.mk_numeral ctx (string_of_int j) 8) (Z3.Z3Array.mk_select ctx array index) in
                    Z3.Z3Array.mk_store ctx array index value
            ) det_updates array in

            match next with
            | Some next -> CHCRule (None,
                [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]],
                Z3.Boolean.mk_and ctx [
                    Z3.Boolean.mk_eq ctx next_ptr (Z3.Arithmetic.mk_add ctx [Z3.Arithmetic.Integer.mk_numeral_i ctx ptr_delta; prev_ptr]);
                    Z3.Boolean.mk_eq ctx next_array array
                ],
                Z3.Expr.mk_app ctx next [next_ptr; next_array]
            ) :: queries_min @ queries_max
            | None -> queries_min @ queries_max
        end
        | LWhile (l1, pred) -> begin
            let label = match get_input_label l1 with
                | None   -> pred
                | Some l -> l
            in

            let l1 = aux_list l1 (Some pred) in

            let phi = Z3.Boolean.mk_eq ctx
                (Z3.BitVector.mk_numeral ctx "0" 8)
                (Z3.Z3Array.mk_select ctx prev_array prev_ptr)
            in


            CHCRule (None,
                [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]],
                Z3.Boolean.mk_not ctx phi,
                Z3.Expr.mk_app ctx label [prev_ptr; prev_array]
            ) :: match next with
            | Some next -> CHCRule (None,
                [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]],
                phi,
                Z3.Expr.mk_app ctx next [prev_ptr; prev_array]
            ) :: l1
            | None -> l1

        end
        | LError pred -> begin
            if config.check_error_loc then
                [CHCQuery (None, [Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]], Z3.Boolean.mk_true ctx)]
            else
                []
        end

    and aux_list ast next = match ast with
        | t :: q -> begin
            match get_input_label q with
            | Some l -> List.fold_right List.cons (aux t (Some l)) (aux_list q next)
            | None   -> aux t next
        end
        | [] -> []
    in

    match get_input_label ast with
    | Some pred -> CHCRule (None, [],
        Z3.Boolean.mk_and ctx [
            Z3.Boolean.mk_eq ctx prev_ptr
                (Z3.Arithmetic.Integer.mk_numeral_i ctx 0);
            Z3.Boolean.mk_eq ctx prev_array
                (Z3.Z3Array.mk_const_array ctx (Z3.Arithmetic.Integer.mk_sort ctx) (Z3.BitVector.mk_numeral ctx "0" 8))
        ],
        Z3.Expr.mk_app ctx pred [prev_ptr; prev_array]
    ) :: aux_list ast None
    | _ -> aux_list ast None



let rec convert (ast: Ast.loc_expr list) : expr list =
    match ast with
    | {expr=Ast.While l1} :: l2 -> begin
        match convert l1, convert l2 with
        | Error :: _, Error :: _ -> [Error]
        | l1, l2 -> While l1 :: l2
    end
    | {expr=Ast.Error} :: _ -> [Error]
    | _ :: _ -> begin
        let rec block_case (new_ptr, det_updates, nondet_updates) (ast: Ast.loc_expr list) = match ast with
        | {expr=Ast.Read}  :: q -> block_case (new_ptr, IntMap.remove new_ptr det_updates, IntSet.add new_ptr nondet_updates) q
        | {expr=Ast.Write} :: q -> block_case (new_ptr, det_updates, nondet_updates) q
        | {expr=Ast.Left}  :: q -> block_case (new_ptr-1, det_updates, nondet_updates) q
        | {expr=Ast.Right} :: q -> block_case (new_ptr+1, det_updates, nondet_updates) q
        | {expr=Ast.Incr}  :: q ->
            if IntSet.mem new_ptr nondet_updates then
                block_case (new_ptr, det_updates, nondet_updates) q
            else if IntMap.mem new_ptr det_updates then
                block_case (new_ptr, IntMap.add new_ptr (1+IntMap.find new_ptr det_updates) det_updates, nondet_updates) q
            else
                block_case (new_ptr, IntMap.add new_ptr 1 det_updates, nondet_updates) q
        | {expr=Ast.Decr}  :: q ->
            if IntSet.mem new_ptr nondet_updates then
                block_case (new_ptr, det_updates, nondet_updates) q
            else if IntMap.mem new_ptr det_updates then
                block_case (new_ptr, IntMap.add new_ptr (IntMap.find new_ptr det_updates-1) det_updates, nondet_updates) q
            else
                block_case (new_ptr, IntMap.add new_ptr (-1) det_updates, nondet_updates) q
        | {expr=Ast.Error} :: _ -> [Error]
        | q -> Block (new_ptr, det_updates, nondet_updates) :: convert q
        in block_case (0, IntMap.empty, IntSet.empty) ast
    end
    | [] -> []

