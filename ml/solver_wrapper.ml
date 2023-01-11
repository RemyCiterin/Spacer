(**
A solver wrapper for work with label encoding,
we can assert formula of the form label => phi or just phi
*)

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
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

open Format
open Utils

(**
an incremental smt wrapper for work with label encoding

a label is a boolean constant

a formula is a pair (label, phi) and represent the formula
label => phi if label is not a none, and phi otherwise

queue is the list of lacaly asserted labels
*)
type solver = {
    ctx              : Z3.context;                             (** z3 context *)
    solver           : Z3.Solver.solver;                       (** current solver *)
    mutable formulas : ((formula option * formula) list) list; (** the list of labels and formulas for each backtrack point *)
    mutable queue    : formula list;                           (** the current set of asserted labels *)
    status           : (formula, bool) Hashtbl.t;              (** the status of each label: asserted or not *)
    count            : (formula, int ) Hashtbl.t;              (** the number of occurence of a label *)
    mutable num_call : int                                     (** total number of call of the solver *)
}

(** delete all the occurence of a label into formula in the solver *)
let delete_formulas_with_label solver label =
    begin
        solver.formulas <- List.map (List.filter (
            function
            | (None  , _) -> true
            | (Some l, _) -> not (Expr.equal l label)
        )) solver.formulas
    end

let replace_formulas_with_label solver label formula =
    begin
        solver.formulas <- List.map (List.filter (
            function
            | (None  , _) -> true
            | (Some l, _) -> not (Expr.equal l label)
        )) solver.formulas;

        solver.formulas <- ((Some label, formula) :: List.hd solver.formulas) :: List.tl solver.formulas
    end

(** return the formula assiciated with a given label *)
let get_formula_of_label solver label =
    begin
        Boolean.mk_and solver.ctx (List.concat (List.map (List.filter_map (
            function
            | (Some l, f) when Expr.equal l label -> Some f
            | _ -> None
        )) solver.formulas))
    end

let get_formulas solver =
    begin
        let formula = Boolean.mk_and solver.ctx (List.concat (List.map (List.map (function
            | (Some l, f) -> Boolean.mk_or solver.ctx [Boolean.mk_not solver.ctx l; f]
            | (None,   f) -> f
        )) solver.formulas)) in

        Boolean.mk_and solver.ctx (formula :: solver.queue)
    end

(** create a new label *)
let create_label solver : formula =
    begin
        let new_label = fresh_variable solver.ctx (Boolean.mk_sort solver.ctx) in

        Hashtbl.replace solver.status new_label false;
        Hashtbl.replace solver.count  new_label 0;

        new_label
    end

(** delete an existing label *)
let delete_label solver label : unit =
    begin
        Hashtbl.remove solver.status label;
        Hashtbl.remove solver.count  label;

        let rec update_queue = function
        | t :: q -> if Expr.equal t label then q else t :: update_queue q
        | [] -> []
        in

        solver.queue <- update_queue solver.queue;

        solver.formulas <- List.map (List.filter (function
        | (Some l, _) when Expr.equal label l -> false | _ -> true
        )) solver.formulas;

        Z3.Solver.add solver.solver [Boolean.mk_not solver.ctx label];
    end

(** add a formula to the current backtrack point *)
let add_formula solver (label: formula option) (phi: formula) =
    begin
        solver.formulas <- ((label, phi) :: List.hd solver.formulas) :: List.tl solver.formulas;

        match label with
        | None   -> Z3.Solver.add solver.solver [phi]
        | Some l -> Z3.Solver.add solver.solver [
            Boolean.mk_or solver.ctx [phi; Boolean.mk_not solver.ctx l]
        ]
    end

(** increase the counter of a given label *)
let increase_count solver label =
    Hashtbl.replace solver.count label (Hashtbl.find solver.count label + 1)

(** decrease the counter of a given label *)
let decrease_count solver label =
    begin
        assert (Hashtbl.find solver.count label > 0);
        Hashtbl.replace solver.count label (Hashtbl.find solver.count label - 1)
    end

(** push a new backtrack point *)
let push solver =
    begin
        Z3.Solver.push solver.solver;
        solver.formulas <- [] :: solver.formulas
    end

(** pop a backtrack point *)
let pop solver = match solver.formulas with
    | _ :: (x :: xs) ->
        begin
            Z3.Solver.pop solver.solver 1;
            solver.formulas <- x :: xs
        end
    | _ -> failwith "no backtrack point to pop"

let get_number_backtrack_point solver =
    List.length (solver.formulas) - 1

(** reset and reload the solver state for performances *)
let reset_solver solver : unit =
    begin
        let formulas = List.rev solver.formulas in
        Z3.Solver.reset solver.solver;
        solver.formulas <- [[]];

        List.iter (fun formulas ->
            List.iter (fun (label, phi) -> add_formula solver label phi) formulas;
            push solver
        ) formulas;
        pop solver
    end

(** initalize a solver with a given context *)
let initial_solver ctx =
    begin
        {
            ctx      = ctx;
            solver   = Z3.Solver.mk_solver ctx None;
            formulas = [[]];
            queue    = [];
            status   = Hashtbl.create 42;
            count    = Hashtbl.create 42;
            num_call = 0
        }
    end

(** check the satisfiability with a given set of assumptions *)
let is_sat_with_assmptions solver assumptions =
    begin
        solver.num_call <- solver.num_call + 1;

        if solver.num_call mod 5000 = 0
            then reset_solver solver
        ;

        let assumptions = ref assumptions in

        Hashtbl.iter (fun l b ->
            if Hashtbl.find solver.count l = 0 then
                assumptions := (if b then l else Boolean.mk_not solver.ctx l) :: !assumptions
        ) solver.status;

        let result = Z3.Solver.check solver.solver !assumptions in

        match result with
        | Z3.Solver.UNSATISFIABLE -> false
        | Z3.Solver.SATISFIABLE   -> true
        | _ -> failwith "unknown result"
    end

(** check if a formula is satisfiable *)
let is_sat solver = is_sat_with_assmptions solver []

(** assert a label into the solver *)
let assert_label solver label =
    begin
        solver.queue <- label :: solver.queue;
        Hashtbl.replace solver.status label true
    end

let reset_labels solver =
    begin
        let rec aux = function
        | t :: q -> Hashtbl.replace solver.status t false; aux q
        | _ -> ()
        in

        aux solver.queue;
        solver.queue <- []
    end

(** compute an unsat core, the last status should be unsat *)
let get_unsat_core solver : (formula, unit) Hashtbl.t =
    begin
        let table = Hashtbl.create 42 in
        let rec aux = function
        | t :: q -> begin
            Hashtbl.replace table t ();
            aux q
        end
        | [] -> ()
        in

        aux (Z3.Solver.get_unsat_core solver.solver);
        table
    end

(** take a list of labels, and return an interpolant between the selected labels and the other formulas *)
let get_interpolant solver labels : formula =
    begin
        let labels = FormulaSet.of_list labels in
        let   selected = ref [] in
        let unselected = ref [] in

        List.iter (List.iter (function
        | (None  , f) -> unselected := f :: !unselected;
        | (Some l, f) -> match (Hashtbl.find solver.count l, Hashtbl.find solver.status l, FormulaSet.mem l labels) with
            | (0, true, true ) ->   selected := l :: Boolean.mk_or solver.ctx [f; Boolean.mk_not solver.ctx l] :: !  selected
            | (0, true, false) -> unselected := l :: Boolean.mk_or solver.ctx [f; Boolean.mk_not solver.ctx l] :: !unselected
            | (n, _, true ) when n > 0 ->   selected := Boolean.mk_or solver.ctx [f; Boolean.mk_not solver.ctx l] :: !  selected
            | (n, _, false) when n > 0 -> unselected := Boolean.mk_or solver.ctx [f; Boolean.mk_not solver.ctx l] :: !unselected
            | _ -> ()
        )) solver.formulas;

        let proof = match Z3.Solver.get_proof solver.solver with
        | None   -> failwith "no proof found"
        | Some p -> p
        in

        List.hd (
            Z3.Interpolation.get_interpolant solver.ctx proof (
                Boolean.mk_and solver.ctx (
                    Z3.Interpolation.mk_interpolant solver.ctx (Boolean.mk_and solver.ctx !selected) :: !unselected
                )
            ) (Z3.Params.mk_params solver.ctx)
        )
    end

let test_solver =
    begin

        let cfg = [("model", "true"); ("proof", "true")] in
        let ctx = Z3.Interpolation.mk_interpolation_context cfg in

        let solver = initial_solver ctx in

        let label_a = create_label solver in
        let label_b = create_label solver in
        let label_c = create_label solver in

        let x = fresh_variable ctx (Boolean.mk_sort ctx) in
        let y = fresh_variable ctx (Boolean.mk_sort ctx) in
        let z = fresh_variable ctx (Boolean.mk_sort ctx) in

        let formula_a =
            Boolean.mk_and ctx [Boolean.mk_not ctx x; Boolean.mk_not ctx y]
        in

        (* Z3.Interpolation.mk_interpolant ctx  *)
        Format.printf "%s %s %s\n" (Expr.to_string x) (Expr.to_string y) (Expr.to_string z);

        let formula_b =
            Boolean.mk_and ctx [x; z]
        in

        let formula_c =
            Boolean.mk_and ctx [y; z]
        in

        let label = create_label solver in
        add_formula solver (Some label  ) (Boolean.mk_or ctx [label_b; label_c]);

        add_formula solver (Some label_b) formula_b;
        add_formula solver (Some label_c) formula_c;
        add_formula solver (Some label_a) formula_a;

        increase_count solver label_c;
        increase_count solver label_b;

        assert_label solver label  ;
        assert_label solver label_a;

        let b = is_sat solver in

        Format.printf "%s\n" (
            match b with |true -> "SAT" |false -> "UNSAT " ^ Expr.to_string
                (get_interpolant solver [label; label_b; label_c])
        );
        Format.print_flush ();
        ()


    end
