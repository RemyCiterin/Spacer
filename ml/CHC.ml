(** Definition of constrained Horn clauses in Z3 *)

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

open Utils


(** Represent a prediate using a function declaration *)
type predicate = func_decl

(** A fact is a formula of the formula of the form P(x1, ..., xn)
with P prediate and x1, ..., xn variables *)
type fact = formula

(**
A query is a formula of the form
    forall x1, ..., xn. P1(x1) & ... & Pn(xn) & phi => false
*)
type query = string option * fact list * formula

(**
A rule is a formula of the form
    forall x0, ..., xn, l. P1(x1) & ... & Pn(xn) & phi(l, x0, ..., xn) => P0(x0)
*)
type rule = string option * fact list * formula * fact

(** a CHC is either a rule either a query *)
type chc =
    | CHCQuery of query
    | CHCRule  of rule

let check ctx (alpha:(formula list * formula) FuncDeclHashtbl.t) = function
    | CHCQuery (_, facts, body) -> begin
        let solver = Z3.Solver.mk_solver ctx None in
        let formula = Boolean.mk_and ctx (List.map (fun f ->
            if FuncDeclHashtbl.mem alpha (get_func_decl f) then begin
                let (args, expr) = FuncDeclHashtbl.find alpha (get_func_decl f) in
                let table = FormulaHashtbl.create 42 in
                List.iter (fun (o, n) -> FormulaHashtbl.replace table o n) (List.combine args (get_args f));

                substitute_and_fresh ctx table expr
            end else Z3.Boolean.mk_true ctx
        ) facts) in

        Z3.Solver.add solver [formula; body];

        match Z3.Solver.check solver [] with
        | Z3.Solver.SATISFIABLE   -> false
        | Z3.Solver.UNSATISFIABLE -> true
        | _ -> failwith ""
    end
    | CHCRule (_, facts, body, head) -> begin
        let solver = Z3.Solver.mk_solver ctx None in
        let formula = Boolean.mk_and ctx (List.map (fun f ->
            if FuncDeclHashtbl.mem alpha (get_func_decl f) then begin
                let (args, expr) = FuncDeclHashtbl.find alpha (get_func_decl f) in
                let table = FormulaHashtbl.create 42 in
                List.iter (fun (o, n) -> FormulaHashtbl.replace table o n) (List.combine args (get_args f));

                substitute_and_fresh ctx table expr
            end else Z3.Boolean.mk_true ctx
        ) facts) in

        Z3.Solver.add solver [formula; body];

        let formula = Boolean.mk_not ctx (
            if FuncDeclHashtbl.mem alpha (get_func_decl head) then begin
                let (args, expr) = FuncDeclHashtbl.find alpha (get_func_decl head) in
                let table = FormulaHashtbl.create 42 in
                List.iter (fun (o, n) -> FormulaHashtbl.replace table o n) (List.combine args (get_args head));

                substitute_and_fresh ctx table expr
            end else Z3.Boolean.mk_true ctx
        ) in

        Z3.Solver.add solver [formula];

        match Z3.Solver.check solver [] with
        | Z3.Solver.SATISFIABLE   -> false
        | Z3.Solver.UNSATISFIABLE -> true
        | _ -> failwith ""
    end

(** print a chc *)
let print_chc = function
    | CHCQuery (_, facts, phi) -> begin
        List.iter (fun f -> Format.printf "%s & " (Expr.to_string f)) facts;
        Format.printf "%s => false" (Expr.to_string phi)
    end
    | CHCRule (_, facts, phi, head) -> begin
        List.iter (fun f -> Format.printf "%s & "(Expr.to_string f)) facts;
        Format.printf "%s => %s" (Expr.to_string phi) (Expr.to_string head)
    end

(** print a constrained Horn clause system with the smtlib2 format *)
let print_chc_smt2 ctx (problem: chc list) : unit =
    begin
        Format.printf "(set-logic HORN)\n\n";

        let declarations : unit FuncDeclHashtbl.t = FuncDeclHashtbl.create 42 in

        let get_declarations = function
        | CHCRule (_, preds, _, head) ->
            begin
                List.iter (fun p -> FuncDeclHashtbl.replace declarations (get_func_decl p) ()) preds;
                FuncDeclHashtbl.replace declarations (get_func_decl head) ()
            end
        | CHCQuery (_, preds, _) ->
            List.iter (fun p -> FuncDeclHashtbl.replace declarations (get_func_decl p) ()) preds
        in

        List.iter get_declarations problem;

        FuncDeclHashtbl.iter (fun pred _ ->
            Format.printf "%s\n" (FuncDecl.to_string pred)
        ) declarations;

        List.iter (function
        | CHCRule (_, preds, phi, head) ->
            begin
                let table = FormulaHashtbl.create 42 in
                List.iter (fun f -> free_variables_with f table) preds;
                free_variables_with head table;
                free_variables_with phi table;

                Format.printf "(assert (forall (";

                FormulaHashtbl.iter (fun v _ ->
                    Format.printf " (%s %s)" (Expr.to_string v) (Sort.to_string (get_sort v))
                ) table;

                Format.printf " ) (=> ";

                Format.printf "%s" (Expr.to_string (
                    Boolean.mk_and ctx (phi :: preds)
                ));
                Format.printf " %s)))\n" (Expr.to_string head);
            end
        | CHCQuery (_, preds, phi) ->
            begin
                let table = FormulaHashtbl.create 42 in
                List.iter (fun f -> free_variables_with f table) preds;
                free_variables_with phi table;

                Format.printf "(assert (forall (";

                FormulaHashtbl.iter (fun v _ ->
                    Format.printf " (%s %s)" (Expr.to_string v) (Sort.to_string (get_sort v))
                ) table;

                Format.printf " ) (=> ";

                Format.printf "%s" (Expr.to_string (
                    Boolean.mk_and ctx (phi :: preds)
                ));
                Format.printf " false)))\n";
            end
        ) problem;

        Format.printf "(check-sat)\n"

    end


(** Generate a fresh predicate with a given context and list of sort for the arguments *)
let fresh_predicate =
    fun ctx args_sort ->
        mk_fresh_func_decl ctx "P" args_sort (Boolean.mk_sort ctx)

(**
Let P1(x1) & ... & Pn(xn) & phi => P0(x0) a rule
and y0 a variable, return a rule
    P1(y1) & ... & Pn(yn) & phi[x := y, l := l'] => P0(y0)
with y1, ..., yn, l' fresh variables
*)
let fresh_rule ctx (rule: rule) (x: formula list) : rule =
    begin
        let (name, predicates, phi, out) = rule in
        let subst = FormulaHashtbl.create 42 in

        List.iter (fun (p, n) -> FormulaHashtbl.replace subst p n) (List.combine (get_args out) x);
        List.iter (fun pred -> if List.length (get_args pred) = 0
            then FormulaHashtbl.replace subst pred pred
        ) predicates;

        if List.length (get_args out) = 0 then
          FormulaHashtbl.replace subst out out;


        (name, List.map (fun p -> substitute_and_fresh ctx subst p) predicates, substitute_and_fresh ctx subst phi, substitute_and_fresh ctx subst out)
    end
