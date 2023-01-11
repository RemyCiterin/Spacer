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

(** For remove ambiguities *)
type formula = Z3.Expr.expr


(** Ordering structure for formula *)
module OrderedFormula = struct
    type t = formula
    let compare f1 f2 = Z3.AST.compare (ast_of_expr f1) (ast_of_expr f2)

    let equal f1 f2 = Z3.Expr.equal f1 f2
    let hash f = Z3.AST.hash (Z3.Expr.ast_of_expr f)
end

module OrderedFuncDecl = struct
  type t = Z3.FuncDecl.func_decl
  let compare f1 f2 = Int.compare (Z3.FuncDecl.get_id f1) (Z3.FuncDecl.get_id f2)
  let equal = Z3.FuncDecl.equal
  let hash = Z3.FuncDecl.get_id
end

(** Map of formulas *)
module FormulaMap = Map.Make (OrderedFormula)
module FormulaSet = Set.Make (OrderedFormula)
module FormulaHashtbl = Hashtbl.Make(OrderedFormula)
module FuncDeclHashtbl = Hashtbl.Make(OrderedFuncDecl)

let get_elem_hashtbl h =
  let result = ref None in
  FormulaHashtbl.iter (fun k _ -> result := Some k) h;
  Option.get !result

(** Return if a given formula is constant *)
let is_constant f : bool =
    begin
        let kind = get_decl_kind (get_func_decl f) in
        match kind with
        | OP_UNINTERPRETED -> get_num_args f = 0
        | _ -> false
    end

(** return if a given formula is a predicate *)
let is_predicate f : bool =
  let kind = get_decl_kind (get_func_decl f) in
  match kind with
  | OP_UNINTERPRETED -> Z3.Boolean.is_bool f
  | _ -> false

(** Return the set of free variables of a formula *)
let free_variables f : unit FormulaHashtbl.t =
    begin
        let table = FormulaHashtbl.create 42 in
        let cache = FormulaHashtbl.create 42 in

        let rec aux term_list = List.iter (fun term -> if not (FormulaHashtbl.mem cache term) then begin
            if is_constant term then FormulaHashtbl.replace table term ();
            FormulaHashtbl.replace cache term ();
            aux (get_args term)
        end) term_list
        in

        aux [f];
        table

    end

let mk_not ctx f = if Z3.Boolean.is_not f then List.hd (get_args f) else Z3.Boolean.mk_not ctx f

(** Return the set of free variables of a formula *)
let free_variables_with f table  =
    begin
        let cache = FormulaHashtbl.create 42 in

        let rec aux term_list = List.iter (fun term -> if not (FormulaHashtbl.mem cache term) then begin
            if is_constant term then FormulaHashtbl.replace table term ();
            FormulaHashtbl.replace cache term ();
            aux (get_args term)
        end) term_list
        in

        aux [f]
    end

(** Generate a fresh variable with a given context and sort *)
let fresh_variable =

    fun ctx sort -> begin
        mk_app ctx (mk_fresh_const_decl ctx "x" sort) []
    end

(** Subtitute the variables of a given formula *)
let rec substitute ctx (table: formula FormulaHashtbl.t) (term: formula) : formula =
    match FormulaHashtbl.find_opt table term with
    | Some term -> term
    | None -> begin
        let new_args = List.map (substitute ctx table) (get_args term) in
        let output   = mk_app ctx (get_func_decl term) new_args        in
        FormulaHashtbl.replace table term output;
        output
    end

let unions sets : FormulaSet.t = match sets with
    | [] -> FormulaSet.empty
    | t :: q ->
        begin
            let output = ref t in

            List.iter (FormulaSet.iter (fun t -> output := FormulaSet.add t !output)) q;
            !output

        end

(**
substitute the variables of a formula with the following substitution
| x when x in hash -> hash x
| x -> fresh with type of x
*)
let rec substitute_and_fresh ctx (table: formula FormulaHashtbl.t) (term: formula) : formula =
    match FormulaHashtbl.find_opt table term with
    | Some term -> term
    | None -> begin
        let output =
            if is_constant term then
                fresh_variable ctx (Z3.Expr.get_sort term)
            else
                let new_args = List.map (substitute_and_fresh ctx table) (get_args term) in
                mk_app ctx (get_func_decl term) new_args
        in

        FormulaHashtbl.replace table term output;
        output
    end

(** transform a formula into a disjunction as maximum as possible *)
let rec to_disjunction_with cache_conj cache_disj ctx formula : FormulaSet.t =
    match formula with
    | _ when Z3.Boolean.is_or formula ->
        unions (List.map (cache_disj ctx) (get_args formula))
    | _ when Z3.Boolean.is_not formula ->
        let f = List.hd (get_args formula) in
        FormulaSet.map (fun f -> mk_not ctx f) (cache_conj ctx f)
    | _ when Z3.Boolean.is_implies formula -> (* a => b := b \/ ~a *)
        let a = List.nth (get_args formula) 0 in
        let b = List.nth (get_args formula) 1 in
        FormulaSet.union (cache_disj ctx (mk_not ctx a)) (cache_disj ctx b)
    | _ -> FormulaSet.singleton formula

(** transform a formula into a conjunction as maximum as possible *)
and to_conjunction_with cache_conj cache_disj ctx formula : FormulaSet.t =
    match formula with
    | _ when Z3.Boolean.is_and formula ->
        unions (List.map (cache_conj ctx) (get_args formula))
    | _ when Z3.Boolean.is_not formula ->
        let f = List.hd (get_args formula) in
        FormulaSet.map (fun f -> mk_not ctx f) (cache_disj ctx f)
    | _ -> FormulaSet.singleton formula

(** transform a formula into a disjunction or conjunction as maximum as possible *)
let (to_disjunction, to_conjunction) =
    let cache_conj = FormulaHashtbl.create 42 in
    let cache_disj = FormulaHashtbl.create 42 in

    let rec cache_conj_fun ctx formula : FormulaSet.t =
        match FormulaHashtbl.find_opt cache_conj formula with
        | None ->
            begin
                let result = to_conjunction_with cache_conj_fun cache_disj_fun ctx formula in
                FormulaHashtbl.replace cache_conj formula result;
                result
            end
        | Some set -> set

    and     cache_disj_fun ctx formula : FormulaSet.t =
        match FormulaHashtbl.find_opt cache_disj formula with
        | None ->
            begin
                let result = to_disjunction_with cache_conj_fun cache_disj_fun ctx formula in
                FormulaHashtbl.replace cache_disj formula result;
                result
            end
        | Some set -> set
    in

    let to_conjunction (ctx:Z3.context) (formula:formula) =
        if FormulaHashtbl.length cache_conj > 1000 then FormulaHashtbl.clear cache_conj;
        if FormulaHashtbl.length cache_disj > 1000 then FormulaHashtbl.clear cache_disj;
        cache_conj_fun ctx formula
    in

    let to_disjunction (ctx:Z3.context) (formula:formula) =
        if FormulaHashtbl.length cache_conj > 1000 then FormulaHashtbl.clear cache_conj;
        if FormulaHashtbl.length cache_disj > 1000 then FormulaHashtbl.clear cache_disj;
        cache_disj_fun ctx formula
    in

    (to_disjunction, to_conjunction)

let is_atom formula =
    Z3.Boolean.is_bool formula &&
    List.for_all Z3.Boolean.is_bool (get_args formula)

type model_with_cache = {
    model: Z3.Model.model;
    cache: bool FormulaHashtbl.t;
    ctx: Z3.context
}

let rec eval_in_model model value =
    let from_bool value =
        if Z3.Boolean.is_true value then true else
            if Z3.Boolean.is_false value then false else
                failwith "not a boolean"
    in

    match FormulaHashtbl.find_opt model.cache value with
    | Some v -> v
    | None -> begin
        let out = match value with
        (*| _ when Z3.Boolean.is_and     value ->
            List.fold_left (&&) true (List.map (eval_in_model model) (get_args value))
        | _ when Z3.Boolean.is_or      value ->
            List.fold_left (||) true (List.map (eval_in_model model) (get_args value))
        | _ when Z3.Boolean.is_xor     value ->
            List.fold_left (<>) true (List.map (eval_in_model model) (get_args value))
        | _ when Z3.Boolean.is_not     value ->
            not (eval_in_model model (List.hd (get_args value)))
        | _ when Z3.Boolean.is_iff     value ->
            let a1 = List.nth (get_args value) 0 in
            let a2 = List.nth (get_args value) 1 in
            eval_in_model model a1 = eval_in_model model a2
        | _ when Z3.Boolean.is_implies value ->
            let a1 = List.nth (get_args value) 0 in
            let a2 = List.nth (get_args value) 1 in
            eval_in_model model a2 || not (eval_in_model model a1)
        | _ when Z3.Boolean.is_distinct value && is_atom value ->
            let a1 = List.nth (get_args value) 0 in
            let a2 = List.nth (get_args value) 1 in
            eval_in_model model a1 <> eval_in_model model a2
        | _ when Z3.Boolean.is_eq value && is_atom value ->
            let a1 = List.nth (get_args value) 0 in
            let a2 = List.nth (get_args value) 1 in
            eval_in_model model a1 = eval_in_model model a2*)
        | _ -> match Z3.Model.eval model.model value true with
            | None -> failwith "error during model evaluation"
            | Some out -> from_bool out
        in
        FormulaHashtbl.replace model.cache value out;
        out
    end

let rec get_under_approx (model : model_with_cache) (formula : formula) =
    begin
        let tab_pos : FormulaSet.t FormulaHashtbl.t = FormulaHashtbl.create 42 in
        let tab_neg : FormulaSet.t FormulaHashtbl.t = FormulaHashtbl.create 42 in

        let rec get_under_pos_with get_pos get_neg formula =
        match formula with
        | _ when Z3.Boolean.is_and formula ->
            unions (List.map get_pos (get_args formula))
        | _ when Z3.Boolean.is_not formula ->
            get_neg (List.hd (get_args formula))
        | _ when Z3.Boolean.is_or  formula ->
            begin
                let rec aux = function
                | [] -> failwith "empty list : invalid model"
                | t :: q when eval_in_model model t -> get_pos t
                | _ :: q -> aux q
                in

                aux (get_args formula)
            end
        | _ -> FormulaSet.singleton formula

        and get_under_neg_with get_pos get_neg formula =
        match formula with
        | _ when Z3.Boolean.is_or  formula ->
            unions (List.map get_neg (get_args formula))
        | _ when Z3.Boolean.is_not formula ->
            get_pos (List.hd (get_args formula))
        | _ when Z3.Boolean.is_and formula ->
            begin
                let rec aux = function
                | [] -> failwith "empty list : invalid model"
                | t :: q when not (eval_in_model model t) -> get_neg t
                | _ :: q -> aux q
                in

                aux (get_args formula)
            end
        | _ -> FormulaSet.singleton (mk_not model.ctx formula)
        in

        let rec get_pos formula =
            match FormulaHashtbl.find_opt tab_pos formula with
            | Some s -> s
            | None ->
                begin
                    let out = get_under_pos_with get_pos get_neg formula in
                    FormulaHashtbl.replace tab_pos formula out;
                    out
                end

        and get_neg formula =
            match FormulaHashtbl.find_opt tab_neg formula with
            | Some s -> s
            | None ->
                begin
                    let out = get_under_neg_with get_pos get_neg formula in
                    FormulaHashtbl.replace tab_neg formula out;
                    out
                end
        in

        get_pos formula
    end
