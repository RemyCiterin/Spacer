open Z3

open Utils
open Ps_ast
open CHC

type 'a tree =
  | Leaf of 'a
  | Node of ('a tree) SMap.t

let rec tree_equality ctx t1 t2 = match (t1, t2) with
  | Leaf f1, Leaf f2 -> Z3.Boolean.mk_eq ctx f1 f2
  | Node m1, Node m2 -> Z3.Boolean.mk_and ctx (
    SMap.fold (fun name _ l -> tree_equality ctx (SMap.find name m1) (SMap.find name m2) :: l) m1 []
  )
  | _ -> failwith ""

let rec expr_to_formula ctx (env: (formula tree) SMap.t) expr = match expr.expr with
  | Const b -> Leaf (if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx)
  | Binop (e1, Xor, e2) ->
    begin
      match (expr_to_formula ctx env e1, expr_to_formula ctx env e2) with
      | (Leaf e1, Leaf e2) -> Leaf (Boolean.mk_xor ctx e1 e2)
      | _ -> failwith ""
    end
  | Binop (e1, And, e2) ->
    begin
      match (expr_to_formula ctx env e1, expr_to_formula ctx env e2) with
      | (Leaf e1, Leaf e2) -> Leaf (Boolean.mk_and ctx [e1; e2])
      | _ -> failwith ""
    end
  | Binop (e1, Or, e2) ->
    begin
      match (expr_to_formula ctx env e1, expr_to_formula ctx env e2) with
      | (Leaf e1, Leaf e2) -> Leaf (Boolean.mk_or ctx [e1; e2])
      | _ -> failwith ""
    end
  | Binop (e1, Eq, e2) ->
    Leaf (tree_equality ctx (expr_to_formula ctx env e1) (expr_to_formula ctx env e2))
  | Unop (Get s, e) ->
    begin
      let e = expr_to_formula ctx env e in
      match e with
      | Node t -> SMap.find s t
      | _ -> failwith ""
    end
  | Unop (Not, e) ->
    begin
      let e = expr_to_formula ctx env e in
      match e with
      | Leaf e -> Leaf (mk_not ctx e)
      | _ -> failwith ""
    end
  | LetIn(name, e1, e2) ->
    begin
      let e1 = expr_to_formula ctx env e1 in
      expr_to_formula ctx (SMap.add name e1 env) e2
    end
  | Variable (name) -> SMap.find name env
  | ITE(e1, e2, e3) ->
    begin
      let e1 = expr_to_formula ctx env e1 in
      let e2 = expr_to_formula ctx env e2 in
      let e3 = expr_to_formula ctx env e3 in

      let e1 = match e1 with
      | Leaf e1 -> e1
      | _ -> failwith ""
      in

      let rec aux e2 e3 = match (e2, e3) with
      | (Leaf e2, Leaf e3) -> Leaf (Boolean.mk_ite ctx e1 e2 e3)
      | (Node e2, Node e3) ->
        Node (SMap.mapi (fun name _ ->
          aux (SMap.find name e2) (SMap.find name e3)
        ) e2)
      | _ -> failwith ""
      in

      aux e2 e3
    end
  | NamedTuple m ->
    Node (SMap.map (expr_to_formula ctx env) m)

let rec variable_ordering (args:'a tree) : 'a list =
  match args with
  | Leaf x -> [x]
  | Node m -> SMap.fold (fun _ args l -> variable_ordering args @ l) m []

let rec ty_to_sort ctx = function
  | TBool -> Leaf (Z3.Boolean.mk_sort ctx)
  | TNamedTuple m -> Node (SMap.map (ty_to_sort ctx) m)

let mk_predicate ctx (ty:ty) (env:ty SMap.t) (num_examples:int) =
  let out_sort  = variable_ordering (ty_to_sort ctx (TNamedTuple env)) in

  let args_sort = variable_ordering (ty_to_sort ctx ty) in

  let bool_sort = Z3.Boolean.mk_sort ctx in
  let real_sort = Z3.Arithmetic.Real.mk_sort ctx in

  let sorts = ref [] in

  for i=0 to num_examples-1 do
    sorts := args_sort @ !sorts;
    sorts :=  out_sort @ !sorts;
  done;

  sorts := real_sort :: !sorts;

  Z3.FuncDecl.mk_func_decl_s ctx (ty_to_string ty) !sorts bool_sort


let rec mk_fresh ctx (ty:ty) : formula tree =
  match ty with
  | TBool -> Leaf (fresh_variable ctx (Z3.Boolean.mk_sort ctx))
  | TNamedTuple m -> Node (SMap.map (mk_fresh ctx) m)

let mk_rule ctx (env:ty SMap.t) (name:string) (primitive:primitive) (num_examples:int) : rule =
  begin
    let Primitive (ty, args, expr) = primitive in

    (* arguments for each examples *)
    let args_tree  = Array.make num_examples SMap.empty in

    for i=0 to num_examples-1 do
      args_tree.(i) <- SMap.map (mk_fresh ctx) env;
    done;

    let predicates = SMap.fold (fun name ty l ->

      let args = ref [] in

      for i=0 to num_examples-1 do
        let inputs = Node (SMap.mapi (fun name _ -> SMap.find name args_tree.(i)) env) in
        args := variable_ordering inputs @ !args;

        args_tree.(i) <- SMap.add name (mk_fresh ctx ty) args_tree.(i);
        args := variable_ordering (SMap.find name args_tree.(i)) @ !args;
      done;

      args := fresh_variable ctx (Z3.Arithmetic.Real.mk_sort ctx) :: !args;

      Z3.Expr.mk_app ctx (mk_predicate ctx ty env num_examples) !args :: l
    ) args [] in

    let output = Array.init num_examples (fun _ ->
      mk_fresh ctx ty
    ) in

    let equalities = ref [] in

    for i=0 to num_examples-1 do
      equalities := begin
        tree_equality ctx output.(i) (expr_to_formula ctx (args_tree.(i)) expr)
      end :: !equalities;
    done;

    let phi = Z3.Boolean.mk_and ctx !equalities in

    let head = mk_predicate ctx ty env num_examples in

    let args = ref [] in

    for i=0 to num_examples-1 do
      let inputs = Node (SMap.mapi (fun name _ -> SMap.find name args_tree.(i)) env) in
      args := variable_ordering inputs @ !args;

      args := variable_ordering output.(i) @ !args;
    done;

    let out_size = fresh_variable ctx (Z3.Arithmetic.Real.mk_sort ctx) in
    args := out_size :: !args;

    let phi = Z3.Boolean.mk_and ctx [phi;
      Z3.Boolean.mk_eq ctx out_size (Z3.Arithmetic.mk_add ctx (
        Z3.Arithmetic.Real.mk_numeral_nd ctx 1 1 :: (List.map (fun p -> List.hd (Z3.Expr.get_args p)) predicates)
      ))
    ] in

    (Some name, predicates, phi, Z3.Expr.mk_app ctx head !args)
  end

let rec const_to_tree ctx = function
  | CBool b -> Leaf (if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx)
  | CNamedTuple m -> Node (SMap.map (const_to_tree ctx) m)

let rec model_to_const ctx model = function
  | Leaf formula ->
    let value = Option.get (Z3.Model.eval model formula true) in
    if Z3.Boolean.is_true value then CBool true
    else if Z3.Boolean.is_false value then CBool false
    else failwith "this value is not a boolean"
  | Node m -> CNamedTuple (SMap.map (model_to_const ctx model) m)

(* transform a dsl into a set of constrained Horn clause *)
let dsl_to_chc (max_size:int) (dsl:dsl) (ctx:Z3.context) : chc list = begin
  let (env, out_ty, primitives, examples, goal) = dsl in

  let phi =  ref [] in
  let pred_args = ref [] in

  List.iter (fun (input, output) ->

    let args = mk_fresh ctx (TNamedTuple env) in
    let out  = mk_fresh ctx out_ty in

    phi := tree_equality ctx (const_to_tree ctx input ) args :: !phi;
    phi := tree_equality ctx (const_to_tree ctx output) out  :: !phi;

    pred_args := variable_ordering args @ !pred_args;
    pred_args := variable_ordering out  @ !pred_args;

  ) examples;

  let size = fresh_variable ctx (Z3.Arithmetic.Real.mk_sort ctx) in
  pred_args := size :: !pred_args;

  phi := Z3.Arithmetic.mk_le ctx size (Z3.Arithmetic.Real.mk_numeral_nd ctx max_size 1) :: !phi;

  CHCQuery (None, [Z3.Expr.mk_app ctx (mk_predicate ctx out_ty env (List.length examples)) !pred_args], Z3.Boolean.mk_and ctx !phi)
  :: SMap.fold (fun name primitive l -> CHCRule (mk_rule ctx env name primitive (List.length examples)) :: l) primitives []

end



let cex_to_circuit (ctx:Z3.context) (dsl:dsl) (cex:Spacer.counter_example) : circuit =
  let (env, out_ty, primitives, examples, goal) = dsl in

  let rec aux = function
    | Spacer.CEX (None, [cex]) -> aux cex
    | Spacer.CEX (Some name, cexs) ->
      let Primitive(ty, args, expr) = SMap.find name primitives in
      let (circuits, _) = SMap.fold (fun name _ (circuits, cexs) ->
        match cexs with
        | [] -> failwith ""
        | cex :: cexs -> begin
          (SMap.add name (aux cex) circuits, cexs)

        end
      ) args (SMap.empty, List.rev cexs) in
      Circuit (name, Primitive (ty, args, expr), circuits)
    | _ -> failwith "invalid counter example"
  in aux cex

let rec print_circuit = function
  | Circuit (name, primitive, m) ->
    begin
      Format.printf "%s {" name;
      SMap.iter (fun name circuit ->
        Format.printf "%s : " name;
        print_circuit circuit;
        Format.printf ";"
      ) m;

      Format.printf "}"
    end

let new_example ctx (dsl:dsl) (circuit:circuit) : example option =
  match dsl with
  | env, out_ty, primitives, exemples, Some goal ->
  begin
    let input_variables  = SMap.map (fun ty -> mk_fresh ctx ty) env in

    let rec circuit_to_formula (env : (formula tree) SMap.t) : circuit -> formula tree = function
    | Circuit (name, Primitive(ty, args, expr), m) ->
      let env = SMap.fold (fun name circuit env ->
        SMap.add name (circuit_to_formula env circuit) env
      ) m env in
      expr_to_formula ctx env expr
    in

    let goal_formula = expr_to_formula ctx input_variables goal in

    let solver = Z3.Solver.mk_solver ctx None in
    Z3.Solver.add solver [
      Z3.Boolean.mk_not ctx (tree_equality ctx (circuit_to_formula input_variables circuit) goal_formula)
    ];

    match Z3.Solver.check solver [] with
    | Z3.Solver.UNSATISFIABLE -> None
    | Z3.Solver.SATISFIABLE ->
      begin
        let model = Option.get (Z3.Solver.get_model solver) in

        print_circuit circuit;
        Format.printf "\n";

        Some (
          CNamedTuple (SMap.map (model_to_const ctx model) input_variables),
          model_to_const ctx model goal_formula
        )
      end
    | _ ->  failwith "unknow"
  end
  | _ -> None

let rec solve_with_goal ctx dsl max_size =
  let solver = Spacer.initial_chc_solver ctx (dsl_to_chc max_size dsl ctx) in
  (*CHC.print_chc_smt2 ctx (dsl_to_chc max_size dsl ctx);*)
  match Spacer.model_checking solver with
  | None -> None
  | Some cex -> begin
    let circuit = cex_to_circuit ctx dsl cex in
    match new_example ctx dsl circuit with
    | Some example -> begin
      let (env, out_ty, primitives, examples, goal) = dsl in
      solve_with_goal ctx (env, out_ty, primitives, example :: examples, goal) max_size
    end
    | None -> Some circuit
  end
