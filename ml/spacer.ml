open Z3
open Z3.AST
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl

open Format
open Utils
open CHC
open Solver_wrapper

let debug_mode = ref 1
let verbose = ref true
let cex_extraction = ref true

type counter_example = CEX of string option * counter_example list

(** representation of a clause *)
type clause = FormulaSet.t
(** rpresentation of a cube *)
type cube   = FormulaSet.t
(** representation of a formula in conjunctive normal form *)
type cnf    = clause  list
(** representation of a formula in disjuncive normal form *)
type dnf    = cube    list

let dnf_to_formula ctx l =
  let l = List.map (
    fun s -> Boolean.mk_and ctx (FormulaSet.fold List.cons s [])
  ) l in Boolean.mk_or ctx l

let cnf_to_formula ctx l =
  let l = List.map (
    fun s -> Boolean.mk_or ctx (FormulaSet.fold List.cons s [])
  ) l in Boolean.mk_and ctx l

(** over approximation of recheable states *)
(**
in particular with some simplifications:
over[i] = mk_and ctx [cnf[i]; cnf[i+1]; ...; cnf[depth]]
use delta encoding
*)
type over_approximation = {
  solver    : solver;           (** current environment *)
  labels    : formula Vector.t; (** label of each frame *)
  variables : formula list;     (** variables of the predicate *)
  cnf       : cnf Vector.t;     (** each frame in conjunctive normal form *)
}


let initial_over solver variables =
  {
      solver    = solver;
      labels    = Vector.init ();
      variables = variables;
      cnf       = Vector.init ()
  }

(** under approximation of recheable states *)
type under_approximation = {
  solver        : solver;          (** current environment *)
  variables     : formula list;    (** variales of the predicate *)
  labels        : formula Vector.t;(** label of the under approximation *)
  dnf           : dnf Vector.t;    (** formula in disjunctive normal form *)
  cex           : (formula option * counter_example) FormulaHashtbl.t
}

let get_under_depth under = Vector.length under.labels - 1
let initial_under solver variables =
  {
    solver    = solver;
    variables = variables;
    labels    = Vector.init ();
    dnf       = Vector.init ();
    cex       = FormulaHashtbl.create 42
  }

let get_counter_example under depth : counter_example =
  if !cex_extraction then begin
    let model = Option.get (Z3.Solver.get_model under.solver.solver) in

    let get_value formula =
      let value = Option.get (Z3.Model.eval model formula true) in

      if Z3.Boolean.is_true value then true
      else if Z3.Boolean.is_false value then false
      else failwith "invalid model value"
    in

    let rec get_cex_from_label label =
      if get_value label then
        match FormulaHashtbl.find_opt under.cex label with
        | Some (Some l, cex) -> begin
          match get_cex_from_label l with
          | Some cex -> Some cex
          | None     -> Some cex
        end
        | Some (None, cex) -> Some cex
        | None -> None
      else None
    in

    Option.get (get_cex_from_label (Vector.get under.labels depth))
  end else CEX (None, [])

let increase_under_depth under =
  begin
    assert (get_number_backtrack_point under.solver = 0);
    let label = Solver_wrapper.create_label under.solver in
    Solver_wrapper.add_formula under.solver (Some label) (Boolean.mk_false under.solver.ctx);
    Vector.push under.labels label;
    Vector.push under.dnf [];
  end

(** add a new under aproximation to the solver *)
let add_under_approximation under (phi: cube) depth (cex:counter_example) =
  begin
    assert (get_number_backtrack_point under.solver = 0);
    while get_under_depth under < depth do increase_under_depth under done;
    for i=depth to get_under_depth under do


      let label = create_label under.solver in

      let conj = Boolean.mk_and under.solver.ctx (FormulaSet.fold List.cons phi []) in

      add_formula under.solver (Some label) (
        Z3.Boolean.mk_or under.solver.ctx [
          Vector.get under.labels i; conj
        ]
      );

      add_formula under.solver (Some (Vector.get under.labels i)) label;
      FormulaHashtbl.replace under.cex label (Some (Vector.get under.labels i), cex);

      increase_count under.solver (Vector.get under.labels i);
      Vector.set under.labels i label;
    done;

    Vector.set under.dnf depth (phi :: Vector.get under.dnf depth)

  end

let get_dnf_at_depth under depth =
  begin
    let dnf = ref [] in
    while get_under_depth under < depth do increase_under_depth under done;

    for i=0 to depth do
      let _dnf_ = Vector.get under.dnf i in
      List.iter (fun cube -> dnf := cube :: !dnf) _dnf_;
    done;

    !dnf
  end

(** return the label of an under approximation  at a given depth *)
let get_under_label (under:under_approximation) depth =
  begin
    while get_under_depth under < depth do increase_under_depth under done;

    Vector.get under.labels depth
  end

(** increase the depth of the over approximation *)
let increase_over_depth (over:over_approximation) =
  begin
    let label = create_label over.solver in
    Vector.push over.labels label;

    Vector.push over.cnf [];

  end

(** return the current depth of search *)
let get_over_depth (over:over_approximation) =
    Vector.length over.labels - 1

(** add a new over approximation to the solver *)
let add_over_approximation (over:over_approximation) (phi: FormulaSet.t) (depth:int) =
  begin
    assert (get_number_backtrack_point over.solver = 0);
    while depth > get_over_depth over do increase_over_depth over done;

    for i=0 to depth do
      (* delete all the clauses less than the new clause *)
      (* and delete their occurences into the solver *)

      let length = List.length (Vector.get over.cnf i) in

      Vector.set over.cnf i (List.filter (fun c ->

        not (FormulaSet.subset phi c)

      ) (Vector.get over.cnf i));

      (*
      if length <> List.length (Vector.get over.cnf i) then begin
        replace_formulas_with_label over.solver
          (Vector.get over.labels i)
          (cnf_to_formula over.solver.ctx (Vector.get over.cnf i))
      end
      *)
    done;

    (* add the new clause *)
    add_formula over.solver
      (Some (Vector.get over.labels depth))
      (Boolean.mk_or over.solver.ctx (FormulaSet.fold List.cons phi []))
    ;

    Vector.set over.cnf depth (phi :: Vector.get over.cnf depth);
  end

(** return the labels for a given depth *)
let get_over_labels (over:over_approximation) depth =
  begin
    while depth > get_over_depth over do increase_over_depth over done;

    let labels = ref [] in

    for i=depth to Vector.length over.labels - 1 do
      labels := Vector.get over.labels i :: !labels
    done;

    !labels
  end

(** return the frame of an over approximation at a given depth *)
let get_frame_at_depth (over:over_approximation) (depth:int) : FormulaSet.t list =
  begin
    while depth > get_over_depth over do increase_over_depth over done;
    Vector.get over.cnf depth
  end

let get_over_at_depth (over:over_approximation) (depth:int) : FormulaSet.t list =
  begin
    while depth > get_over_depth over do increase_over_depth over done;
    let result = ref [] in

    for i=depth to Vector.length over.labels - 1 do
      List.iter (fun frame -> result := frame :: !result) (Vector.get over.cnf i)

    done;

    !result
  end

let get_under_label under depth =
  begin
    while get_under_depth under < depth do increase_under_depth under done;
    Vector.get under.labels depth
  end


(** proof obligation *)
type pob = {depth: int; formula: formula; fact: fact}

(** A data structure for test if a pob is blocked *)
type blocker = {
  rules         : rule list;                     (** a constrained Horn clause *)
  solver        : solver;                        (** wrapper of the SMT solver *)
  labels        : formula list;                  (** labels for the body of the rules *)
  fact          : fact;                          (** predicate of te head of each rules *)
  under         : under_approximation list list; (** under approximation of the predicates *)
  over          : over_approximation list list;  (** over approximation of the predicates *)
  mutable pob   : pob option;                    (** current pob *)
}

let complete_frames (blocker:blocker) depth (frames:(formula list * FormulaSet.t list) FuncDeclHashtbl.t) =
  begin
    List.iter (fun ((_, facts, _, _), over) ->

      List.iter (fun (fact, over) ->
        if not (FuncDeclHashtbl.mem frames (get_func_decl fact)) then
          FuncDeclHashtbl.replace frames (get_func_decl fact) (
            get_args fact, get_frame_at_depth over depth
          )
      ) (List.combine facts over)

    ) (List.combine blocker.rules blocker.over)
  end

(** intialize a blocker *)
let initial_blocker solver rules =
  begin
    assert (List.length rules > 0);
    let variables =
      let (_, _, _, h) = List.hd rules in
      get_args h
    in


    let fact = let (_, _, _ , h) = List.hd rules in h in

    let rules = List.map (fun rule -> fresh_rule solver.ctx rule (get_args fact)) rules in

    let under = List.map (fun (_, preds, _, _) -> List.map (fun p ->
      initial_under solver (get_args p)
    ) preds) rules in

    let over  = List.map (fun (_, preds, _, _) -> List.map (fun p ->
      initial_over  solver (get_args p)
    ) preds) rules in

    let labels = List.map (fun (_, _, phi, _) ->
      let label = create_label solver in
      Solver_wrapper.add_formula solver (Some label) phi;
      label
    ) rules in

    {
      rules     = rules;
      solver    = solver;
      labels    = labels;
      under     = under;
      over      = over;
      pob       = None;
      fact      = fact;
    }
  end

(** create a pob *)
let create_pob blocker formula variales depth : pob =
  begin
    let table = FormulaHashtbl.create 42 in

    List.iter (fun (p, n) -> FormulaHashtbl.replace table p n) (List.combine variales (get_args blocker.fact));

    let formula = substitute_and_fresh blocker.solver.ctx table formula in

    {depth = depth; formula = formula; fact = blocker.fact}
  end

(** add an over approximation to a blocker *)
let add_over_approximation_blocker blocker fact phi depth =
  begin
    List.iter (fun ((_, preds, _, _), over) ->
      List.iter (fun (p, over) ->
      if FuncDecl.equal (get_func_decl fact) (get_func_decl p) then
        let table = FormulaHashtbl.create 42 in
        List.iter (
          fun (o, n) -> FormulaHashtbl.replace table o n
        ) (List.combine (get_args fact) (get_args p));
        let phi = FormulaSet.map (substitute_and_fresh blocker.solver.ctx table) phi in
        add_over_approximation over phi depth
      ) (List.combine preds over)
    ) (List.combine blocker.rules blocker.over)
  end

(** add an under approximation to a blocker *)
let add_under_approximation_blocker blocker fact phi depth cex =
  begin
    List.iter (fun ((_, preds, _, _), under) ->
      List.iter (fun (p, under) ->
      if FuncDecl.equal (get_func_decl fact) (get_func_decl p) then
        let table = FormulaHashtbl.create 42 in
        List.iter (
          fun (o, n) -> FormulaHashtbl.replace table o n
        ) (List.combine (get_args fact) (get_args p));
        let phi = FormulaSet.map (substitute_and_fresh blocker.solver.ctx table) phi in
        add_under_approximation under phi depth cex
      ) (List.combine preds under)
    ) (List.combine blocker.rules blocker.under)
  end

(** increase the depth of a pob *)
let increase_depth_pob pob max_depth : pob option =
  if pob.depth = max_depth then None else
    Some {depth=pob.depth+1; formula=pob.formula; fact=pob.fact}

(** set the depth and the pob of the blocker *)
let set_pob blocker (pob: pob option) =
  match pob with
  | Some pob ->
    begin
      (* set the pob of the blocker *)
      blocker.pob <- Some pob;

      (* push the backtrack point *)
      Solver_wrapper.push blocker.solver;

      (* reset the labels of the solver *)
      Solver_wrapper.reset_labels blocker.solver;

      (* add the pob to the solver *)
      Solver_wrapper.add_formula blocker.solver None pob.formula
    end
  | None ->
    begin
      (* set the pob of the blocker *)
      blocker.pob <- None;

      (* pop a batrack point *)
      Solver_wrapper.pop blocker.solver
    end

let is_blocked_debug (blocker:blocker) (formulas:formula list) (depth:int) : bool =
  begin

    let dnf = List.filter_map (fun ((_, _, phi, _), over) ->

      if depth > 0 || List.length over = 0 then Some (FormulaSet.of_list (phi ::
        List.map (fun o -> cnf_to_formula blocker.solver.ctx (get_over_at_depth o (depth-1))) over
      )) else None

    ) (List.combine blocker.rules blocker.over) in

    let dnf = dnf_to_formula blocker.solver.ctx dnf in

    let solver = Z3.Solver.mk_solver blocker.solver.ctx None in

    Z3.Solver.add solver (dnf :: formulas);

    match Z3.Solver.check solver [] with
    | Z3.Solver.UNSATISFIABLE -> true
    | Z3.Solver.SATISFIABLE -> false
    | _ -> failwith "unknow"

  end

(** return if a set of formula is blocker and eventualy a blocked subset of the input formulas *)
let is_blocked (blocker:blocker) (formulas:formula list) (depth:int) : (formula list) option =
  begin
    let labels = List.map (fun _ ->
      fresh_variable blocker.solver.ctx (Z3.Boolean.mk_sort blocker.solver.ctx)
    ) formulas in

    let labeled_formulas = List.map (fun (label, formula) ->
      Z3.Boolean.mk_or blocker.solver.ctx
        [formula; mk_not blocker.solver.ctx label]
    ) (List.combine labels formulas) in

    let pob = {
      formula = Z3.Boolean.mk_and blocker.solver.ctx labeled_formulas;
      fact  = blocker.fact;
      depth = depth;
    } in

    set_pob blocker (Some pob);

    let dnf = List.filter_map (
      fun (l, o) ->
        if List.length o = 0 || depth > 0 then
          Some (l :: List.concat (List.map (fun o -> get_over_labels o (depth - 1)) o))
        else None
    ) (List.combine blocker.labels blocker.over) in

    List.iter (List.iter (Solver_wrapper.increase_count blocker.solver)) dnf;

    let formula = Z3.Boolean.mk_or blocker.solver.ctx (
      List.map (Z3.Boolean.mk_and blocker.solver.ctx) dnf
    ) in

    Solver_wrapper.add_formula blocker.solver None formula;
    Solver_wrapper.reset_labels blocker.solver;

    let result = Solver_wrapper.is_sat_with_assmptions blocker.solver labels in
    List.iter (List.iter (Solver_wrapper.decrease_count blocker.solver)) dnf;


    if not result then begin
      if !debug_mode > 1 then assert ( is_blocked_debug blocker formulas depth );
      let core = get_unsat_core blocker.solver in

      set_pob blocker None;

      Some (List.filter_map (fun (label, formula) ->
        if Hashtbl.mem core label then Some formula else None
      ) (List.combine labels formulas))
    end else begin
      set_pob blocker None;
      None
    end
  end

(** search if a given state have a predecessor *)
let block blocker (pob:pob) : (formula list) option * pob option * (formula list * counter_example) option =
  begin
    (*
    return a new proof obligation if this state have a predecessor
    return a new over-approximation if this state dosn't have a predecessor
    return a new under-approximation if this state is recheable
    *)

    set_pob blocker (Some pob);

    let itp = ref None in
    let und = ref None in
    let out_pob = ref None in
    let unrecheable = ref true in

    let rec aux rule_list label_list under_list over_list =
      match (rule_list, label_list, under_list, over_list) with
      | ((rule_name, facts, phi, _) :: rule_list, label :: label_list, under :: under_list, over :: over_list) ->

          if pob.depth > 0 || List.length over = 0 then begin
          (* assert (List.length over <= 1); *)

          if (List.length over = 0) then begin

            Solver_wrapper.reset_labels blocker.solver;
            Solver_wrapper.assert_label blocker.solver label;

            let result = Solver_wrapper.is_sat blocker.solver in

            if result then begin
              unrecheable := false;
              und := Some ([phi], CEX (rule_name, []));
            end else
              aux rule_list label_list under_list over_list

          end else begin
            let table = FormulaHashtbl.create 42 in

            let pivot = ref None in

            List.iter
              (fun (f, (o, u)) -> FormulaHashtbl.replace table f (o, u))
            (List.combine facts (List.combine over under));

            let under = table in
            let over  = FormulaHashtbl.create 42 in

            let rec process () = begin
              Solver_wrapper.reset_labels blocker.solver;
              Solver_wrapper.assert_label blocker.solver label;

              FormulaHashtbl.iter (fun f (o, _) ->
                let labels = get_over_labels o (pob.depth-1) in
                List.iter (Solver_wrapper.assert_label blocker.solver) labels;
              ) over;

              FormulaHashtbl.iter (fun f (_, u) ->
                Solver_wrapper.assert_label blocker.solver (get_under_label u (pob.depth-1));
              ) under;

              let result = Solver_wrapper.is_sat blocker.solver in

              if result then begin

                unrecheable := false;


                match !pivot with
                | None   ->
                  let cex = CEX (
                    rule_name,
                    List.map (fun f ->
                      let (_, u) = FormulaHashtbl.find under f in
                      get_counter_example u (pob.depth-1)
                    ) facts
                  ) in
                  und := Some (FormulaHashtbl.fold (fun f (_, u) conj ->
                    dnf_to_formula blocker.solver.ctx (get_dnf_at_depth u (pob.depth-1)) :: conj
                  ) under [phi], cex)

                | Some pivot -> begin
                  let cube = ref [phi; pob.formula] in

                  FormulaHashtbl.iter (fun f (_, u) ->
                    if f <> pivot then cube :=
                      dnf_to_formula blocker.solver.ctx (get_dnf_at_depth u (pob.depth-1)) :: !cube;
                  ) under;

                  FormulaHashtbl.iter (fun f (o, u) ->
                    if f <> pivot then cube :=
                      cnf_to_formula blocker.solver.ctx (get_over_at_depth o (pob.depth-1)) :: !cube;
                  ) over;

                  out_pob := Some {
                    formula = Z3.Boolean.mk_and blocker.solver.ctx !cube;
                    depth   = pob.depth-1;
                    fact    = pivot;
                  };
                end

              end else if FormulaHashtbl.length under <> 0 then begin


                let fact = get_elem_hashtbl under in
                let (o, u) = FormulaHashtbl.find under fact in
                FormulaHashtbl.replace over fact (o, u);
                FormulaHashtbl.remove under fact;
                pivot := Some fact;
                process ()
              end
            end in

            process ();

            if !unrecheable then
              aux rule_list label_list under_list over_list
          end
        end else aux rule_list label_list under_list over_list
      | _ -> ()
    in

    aux blocker.rules blocker.labels blocker.under blocker.over;

    (* compute interpolant *)
    if !unrecheable then begin

      (* compute the dnf of labels *)
      let dnf = List.filter_map (
        fun (l, o) ->
          if
            List.length o = 0 || pob.depth > 0
          then
            Some (l :: List.concat (List.map (fun o -> get_over_labels o (pob.depth - 1)) o))
          else
            None
      ) (List.combine blocker.labels blocker.over) in

      (* increase the depth of the labels in the dnf *)
      List.iter (List.iter (Solver_wrapper.increase_count blocker.solver)) dnf;

      let formula = Z3.Boolean.mk_or blocker.solver.ctx (
        List.map (Z3.Boolean.mk_and blocker.solver.ctx) dnf
      ) in

      let label = Solver_wrapper.create_label blocker.solver in
      Solver_wrapper.add_formula blocker.solver (Some label) formula;

      Solver_wrapper.reset_labels blocker.solver;
      Solver_wrapper.assert_label blocker.solver label;

      let result = Solver_wrapper.is_sat blocker.solver in

      assert (result = false);

      let labels = label :: List.concat dnf in



      let _ =
        try itp := Some (FormulaSet.fold List.cons
            (Utils.to_disjunction blocker.solver.ctx
              (Solver_wrapper.get_interpolant blocker.solver labels)
            ) []
          )
        with Z3.Error _ -> raise (Z3.Error "interpolation error")
      in

      Solver_wrapper.delete_label blocker.solver label;

      (* decrease the depth of the labels in the dnf *)
      List.iter (List.iter (Solver_wrapper.decrease_count blocker.solver)) dnf;

    end;

    set_pob blocker None;

    if !unrecheable then begin

      let formulas = List.map (mk_not blocker.solver.ctx) (Option.get !itp) in
      let result = is_blocked blocker formulas pob.depth in

      assert(Option.is_some result);

      (*
      itp := Some (
        List.map (mk_not blocker.solver.ctx) (Option.get result)
      );
      *)

    end;

    (!itp, !out_pob, !und)
  end

(** pob comparison *)
module ComparePOB = struct
  type t = pob

  let compare q1 q2 =
    begin
      let c_depth = Int.compare q1.depth q2.depth in
      let c_formula = compare q1.formula q2.formula in

      if c_depth = 0 then
        if c_formula = 0 then compare q1.fact q2.fact else c_formula else c_depth
    end
end

(** set of proof obligations *)
module POBSet = Stdlib.Set.Make(ComparePOB)

(** map of proof obligations *)
module POBMap = Stdlib.Map.Make(ComparePOB)

(** a CHCs solver type *)
type chc_solver = {
  ctx      : Z3.context;
  query    : predicate;
  blockers : blocker FuncDeclHashtbl.t;
  mutable pob_set  : POBSet.t;

  chc_list : CHC.chc list;
}

let initial_chc_solver ctx chc_list =
  begin
    let solver  = initial_solver ctx in
    let queries = List.filter_map (function | CHCQuery q -> Some q | CHCRule _ -> None) chc_list in
    let rules   = List.filter_map (function | CHCQuery _ -> None | CHCRule r -> Some r) chc_list in
    let queries = if List.length queries = 0 then [(None, [], Z3.Boolean.mk_false ctx)] else queries in

    let blockers = FuncDeclHashtbl.create 42 in

    let predicates = List.map (
      fun (_, _, _, h) -> get_func_decl h
    ) rules in

    List.iter (fun p ->
      if not (FuncDeclHashtbl.mem blockers p) then
        let blocker_rules = List.filter_map (
          fun (name, preds, phi, head) ->
            if Z3.FuncDecl.equal (get_func_decl head) p
            then Some (name, preds, phi, head)
            else None
        ) rules in

        let s = initial_solver ctx in
        let blocker = initial_blocker s blocker_rules in
        assert (Z3.FuncDecl.equal (get_func_decl blocker.fact) p);
        FuncDeclHashtbl.replace blockers p (initial_blocker s blocker_rules)
    ) predicates;

    (* separate the queries by predicate *)

    let query_pred = CHC.fresh_predicate ctx [] in

    let query = initial_blocker solver (List.map (
      fun (name, preds, phi) -> (name, preds, phi, mk_app ctx query_pred [])
    ) queries) in

    FuncDeclHashtbl.replace blockers query_pred query;

    {
      ctx = ctx;
      query = query_pred;
      pob_set = POBSet.empty;
      blockers = blockers;
      chc_list = chc_list;
    }
  end

(**
add a new over approximation, assume under[i] => clause for i in {0, ..., depth} and
phi & over[facts, depth-1] => clause for all clauses of the form (phi, facts, fact)
*)
let add_over_approximation_chc_solver chc_solver fact clause depth =
  begin
    FuncDeclHashtbl.iter (fun pred b ->

      if FuncDecl.equal pred (get_func_decl fact) && !debug_mode > 0 then begin

        let table = FormulaHashtbl.create 42 in
        List.iter (fun (p, n) ->
          FormulaHashtbl.replace table p n
        ) (List.combine (get_args fact) (get_args b.fact));

        let cube = FormulaSet.fold (fun f l ->
          mk_not chc_solver.ctx (substitute_and_fresh chc_solver.ctx table f) :: l
        ) clause [] in

        assert (Option.is_some (is_blocked b cube depth));



      end;

      add_over_approximation_blocker b fact clause depth
    ) chc_solver.blockers
  end

(**
add an under approximation, assume cube => over[i] for i in {depth, MaxDepth} and
cube(head) => exists (phi & under[i, facts]) (get_args head) for all (facts, phi, head) rule

exists phi X is equivalent to an existential quantifier on all the
variables of phi different to X
*)
let add_under_approximation_chc_solver chc_solver fact cube depth cex =
  begin
    FuncDeclHashtbl.iter (fun _ b ->
      add_under_approximation_blocker b fact cube depth cex
    ) chc_solver.blockers
  end

let bounded_model_checking (chc_solver:chc_solver) depth : counter_example option =
  begin
    FuncDeclHashtbl.iter (fun _ b ->
      List.iter (fun (under, over) ->
        List.iter (fun (under, over) ->
          while get_under_depth under < depth do increase_under_depth under done;
          while get_over_depth  over  < depth do increase_over_depth  over  done;
        ) (List.combine under over)
      ) (List.combine b.under b.over)

    ) chc_solver.blockers;

    let init_pob = {
      fact = mk_app chc_solver.ctx chc_solver.query [];
      formula = Boolean.mk_true chc_solver.ctx;
      depth = depth;
    } in

    chc_solver.pob_set <- POBSet.singleton init_pob;


    while not (POBSet.is_empty chc_solver.pob_set) do

      let pob = POBSet.min_elt chc_solver.pob_set in
      chc_solver.pob_set <- POBSet.remove pob chc_solver.pob_set;

      (*
      Format.printf "query depth: %d\n" pob.depth;
      Format.printf "fact: %s\n" (Expr.to_string pob.fact);
      (*Format.printf "expr: %s\n" (Expr.to_string pob.formula);*)
      Format.print_flush ();
      *)

      match FuncDeclHashtbl.find_opt chc_solver.blockers (get_func_decl pob.fact) with
      | None -> begin
        (* get_args pob.fact doesn't have predecessor *)
        add_over_approximation_chc_solver chc_solver pob.fact FormulaSet.empty pob.depth
      end
      | Some blocker ->
        begin
          match block blocker pob with
          | Some itp, None, None -> begin
            if pob.depth < depth then
              chc_solver.pob_set <- POBSet.add
              {formula=pob.formula;depth=pob.depth+1;fact=pob.fact}
              chc_solver.pob_set
            ;

            add_over_approximation_chc_solver chc_solver pob.fact (FormulaSet.of_list itp) pob.depth
          end
          | None, None, Some (und, cex) -> begin
            let model = {
              ctx = chc_solver.ctx;
              model = Option.get (Z3.Solver.get_model blocker.solver.solver);
              cache = FormulaHashtbl.create 42
            } in
            let und = unions (List.map (get_under_approx model) und) in
            add_under_approximation_chc_solver chc_solver pob.fact und pob.depth cex

          end
          | None, Some out_pob, None -> begin
              let model = {
                ctx = chc_solver.ctx;
                model = Option.get (Z3.Solver.get_model blocker.solver.solver);
                cache = FormulaHashtbl.create 42
              } in

              let out_pob = {
                fact  = out_pob.fact;
                depth = out_pob.depth;
                formula =
                  Z3.Boolean.mk_and chc_solver.ctx (
                    FormulaSet.elements (
                      get_under_approx model out_pob.formula
                    )
                  )
              } in


              chc_solver.pob_set <- POBSet.add pob chc_solver.pob_set;

              match FuncDeclHashtbl.find_opt chc_solver.blockers (get_func_decl out_pob.fact) with
              | Some b ->
                chc_solver.pob_set <- POBSet.add (
                  create_pob b out_pob.formula (get_args out_pob.fact) out_pob.depth
                ) chc_solver.pob_set
              | None ->
                (* get_args out_pob.fact doesn't have predecessor *)

                add_over_approximation_chc_solver chc_solver out_pob.fact FormulaSet.empty out_pob.depth
          end
          | _ -> failwith "block give an incoherent result"
        end
    done;

    match block (FuncDeclHashtbl.find chc_solver.blockers chc_solver.query) init_pob with
    | (None, None, Some (_, cex)) -> Some cex
    | (Some _, None, None) -> None
    | (None, Some _, None) -> failwith "block give no result"
    | _ -> failwith "block give incoherent result"
  end

let propagate (chc_solver:chc_solver) (depth:int) =
  begin
    (* 1. generate the list formula to test *)
    let frames = FuncDeclHashtbl.create 42 in

    FuncDeclHashtbl.iter (fun _ blocker ->
      complete_frames blocker depth frames
    ) chc_solver.blockers;

    let n = ref 0 in
    FuncDeclHashtbl.iter (fun _ (_, frame) -> n := !n + List.length frame) frames;

    if !verbose then Format.printf "%d " !n;

    let is_fixed_point = ref true in

    let mk_not formula = if Z3.Boolean.is_not formula
      then
        List.hd (get_args formula)
      else
        Z3.Boolean.mk_not chc_solver.ctx formula
    in

    FuncDeclHashtbl.iter (fun pred (args, frame) -> List.iter (fun formula_set ->
      (* try to block the clause at the depth `depth+1` *)

      match FuncDeclHashtbl.find_opt chc_solver.blockers pred with
      | Some blocker -> begin

        let table = FormulaHashtbl.create 42 in

        List.iter (fun (new_var, old_var) ->
          FormulaHashtbl.replace table old_var new_var
        ) (List.combine (get_args blocker.fact) args);

        let formula_list = FormulaSet.fold (fun f l ->
          substitute_and_fresh chc_solver.ctx table (mk_not f) :: l
        ) formula_set [] in

        let result = is_blocked blocker formula_list (depth+1) in

        match result with
        | Some new_list -> begin
          let new_list = List.map mk_not new_list in
          add_over_approximation_chc_solver chc_solver blocker.fact (FormulaSet.of_list new_list) (depth+1)
        end
        | None -> is_fixed_point := false

      end
      | None -> begin
        add_over_approximation_chc_solver chc_solver (mk_app chc_solver.ctx pred args) FormulaSet.empty (depth+1)
      end
    ) frame) frames;

    !is_fixed_point
  end

let model_checking chc_solver : counter_example option =
  let rec aux depth =
    match bounded_model_checking chc_solver depth with
    | Some cex -> Some cex
    | None ->
    begin

      let is_fixed_point = ref false in

      if !verbose then begin
        Format.printf "no counterexample found at depth %d\n" depth;
        Format.print_flush ();
      end;

      for i=0 to depth-1 do
        if not !is_fixed_point then begin
          is_fixed_point := propagate chc_solver i;


          if !is_fixed_point && !debug_mode > 0 then begin
            let frames = FuncDeclHashtbl.create 42 in

            FuncDeclHashtbl.iter (fun _ blocker ->
              for j=i to depth+1 do
                complete_frames blocker depth frames
              done;
            ) chc_solver.blockers;

            let table = FuncDeclHashtbl.create 42 in

            FuncDeclHashtbl.iter (fun pred (args, frame) ->
              FuncDeclHashtbl.replace table pred (args, (Z3.Boolean.mk_and chc_solver.ctx (
                List.map (fun c ->
                  Z3.Boolean.mk_or chc_solver.ctx (
                    FormulaSet.fold List.cons c []
                  )
                ) frame
              )))
            ) frames;

            Format.printf "\n";

            List.iter (fun chc ->
              match chc with
              | CHCQuery (_, _, _) ->
                Format.printf "inv: %b\n" (CHC.check chc_solver.ctx table chc)
              | CHCRule (_, _, _, head) ->
                Format.printf "inv %s: %b\n"
                  (Z3.Symbol.to_string (Z3.FuncDecl.get_name (get_func_decl head)))
                  (CHC.check chc_solver.ctx table chc);
              Format.print_flush ();
            ) chc_solver.chc_list;

            List.iter (fun chc ->
              match chc with
              | CHCQuery (_, _, _) -> ()
              | CHCRule (_, _, _, head) ->
                if not (CHC.check chc_solver.ctx table chc) then begin
                  print_chc chc; Format.printf "\n"; Format.print_flush ();
                end
            ) chc_solver.chc_list;
          end

          end
      done;
      if not !is_fixed_point then begin
        let _ = propagate chc_solver depth in

        if !verbose then begin
        Format.printf "\n"; Format.print_flush ();
      end end;

      if !is_fixed_point then None else aux (depth+1)
    end
  in

  aux 0
