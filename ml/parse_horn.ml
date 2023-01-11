open Z3
open CHC
open Utils

exception Parsing_error of string

let cfg = [("model", "true"); ("proof", "true")]
let ctx = mk_context cfg


let parse_file (ctx:Z3.context) (filename: string) =
  begin
    let file : formula = Z3.SMT.parse_smtlib2_file ctx filename [] [] [] [] in
    let formula_set = to_conjunction ctx file in


    let is_quantifier f =
      let ast = Z3.Expr.ast_of_expr f in
      Z3.AST.is_quantifier ast
    in

    let formula_to_chc formula sorts =
      let new_vars = List.map (fun sort -> fresh_variable ctx sort) sorts in
      let formula = Z3.Expr.substitute_vars formula (List.rev new_vars) in

      let formulas = to_disjunction ctx formula in

      let new_vars = FormulaSet.of_list new_vars in

      let neg_predicates = FormulaSet.filter_map (fun f ->
        if Z3.Boolean.is_not f then
          let f = List.hd (Z3.Expr.get_args f) in
          if is_predicate f && not (FormulaSet.mem f new_vars) then Some (f) else None
        else None
      ) formulas in

      let pos_predicates = FormulaSet.filter_map (fun f ->
        if is_predicate f && not (FormulaSet.mem f new_vars) then Some f else None
      ) formulas in

      let formula = ref (FormulaSet.filter_map (fun f ->
        if Z3.Boolean.is_not f then
          let f = List.hd (Z3.Expr.get_args f) in
          if is_predicate f && not (FormulaSet.mem f new_vars) then None else Some f
        else
          if is_predicate f && not (FormulaSet.mem f new_vars) then None else Some (mk_not ctx f)
      ) formulas) in
      let pos_predicates = FormulaSet.map (fun f ->
        let args = Z3.Expr.get_args f in

        let table = FormulaHashtbl.create 42 in

        let args = List.map (fun a ->
          if is_constant a && not (FormulaHashtbl.mem table a) then begin
            if is_constant a then FormulaHashtbl.replace table a (); a
          end else begin
            let b = fresh_variable ctx (Z3.Expr.get_sort a) in
            formula := FormulaSet.add (Z3.Boolean.mk_eq ctx a b) !formula;
            b
          end
        ) args in

        Z3.Expr.mk_app ctx (Z3.Expr.get_func_decl f) args

      ) pos_predicates in


      let neg_predicates = FormulaSet.map (fun f ->
        let args = Z3.Expr.get_args f in

        let table = FormulaHashtbl.create 42 in

        let args = List.map (fun a ->
          if is_constant a && not (FormulaHashtbl.mem table a) then begin
            if is_constant a then FormulaHashtbl.replace table a (); a
          end else begin
            let b = fresh_variable ctx (Z3.Expr.get_sort a) in
            formula := FormulaSet.add (Z3.Boolean.mk_eq ctx a b) !formula;
            b
          end
        ) args in

        Z3.Expr.mk_app ctx (Z3.Expr.get_func_decl f) args

      ) neg_predicates in

      if FormulaSet.cardinal pos_predicates > 1 then
        raise (Parsing_error "the number of positive predicates is greater that 1")
      else if FormulaSet.cardinal pos_predicates = 1 then
        CHCRule (None,
          FormulaSet.fold List.cons neg_predicates [],
          Z3.Boolean.mk_and ctx (FormulaSet.fold List.cons !formula []),
          FormulaSet.min_elt pos_predicates
        )
      else
        CHCQuery (None,
          FormulaSet.fold List.cons neg_predicates [],
          Z3.Boolean.mk_and ctx (FormulaSet.fold List.cons !formula [])
        )
    in

    let chc_list = ref [] in

    let _ = FormulaSet.iter (fun f ->

      chc_list := (
        (* soit la formule est de la forme (forall ... (...)), soit elle est de la forme (not (exists ... (...))) *)
        if is_quantifier f then begin
          let q = Z3.Quantifier.quantifier_of_expr f in

          if not (Z3.Quantifier.is_existential q) then
            formula_to_chc (Z3.Quantifier.get_body q) (Z3.Quantifier.get_bound_variable_sorts q)
          else raise (Parsing_error "the file contain existentialy quantified formulas")

        end else if Z3.Boolean.is_not f then begin
          let f = List.hd (Z3.Expr.get_args f) in

          if is_quantifier f
          then
            let q = Z3.Quantifier.quantifier_of_expr f in
            if Z3.Quantifier.is_existential q
            then formula_to_chc (mk_not ctx (Z3.Quantifier.get_body q)) (Z3.Quantifier.get_bound_variable_sorts q)
            else raise (Parsing_error "the file contain existentialy quantified formulas")
          else
            formula_to_chc (mk_not ctx f) []

        end else formula_to_chc f []
      ) :: !chc_list
    ) formula_set in

    !chc_list
  end

let _ =
  begin
    let chc_list = parse_file ctx "./tests/test.smt2" in
    (*CHC.print_chc_smt2 ctx chc_list;*)


    let chc_solver = Spacer.initial_chc_solver ctx chc_list in

    let result = Spacer.model_checking chc_solver in
    Format.printf "%b\n" (Option.is_none result);
    Format.print_flush ()
  end

