(** AST for DSL description *)

(** for the moment, this DSL constructor is only for boolean *)
open Lexing
open Parsing
type position = Lexing.position * Lexing.position

module SSet = Set.Make (String)

module SMap = Map.Make (String)

type ty =
  | TBool
  | TNamedTuple of ty SMap.t

and const =
  | CBool of bool               (** `CBool b` represent the boolean constant `b` *)
  | CNamedTuple of const SMap.t

and expr = {ty: ty; loc: position; expr: expr expr_internal}

and 'a expr_internal =
  | Binop      of 'a * binop * 'a
  | LetIn      of string * 'a * 'a
  | Unop       of unop * 'a
  | Const      of bool
  | ITE        of 'a * 'a * 'a
  | NamedTuple of 'a SMap.t
  | Variable   of string

and unop =
  | Get of string
  | Not

and binop =
  | And (* boolean operations *)
  | Or
  | Xor
  | Eq  (* anytype operations *)

and variable = string * ty

and primitive =
  | Primitive of ty * ty SMap.t * expr

and example = const * const

and goal = expr

and dsl =
  ty SMap.t * ty * primitive SMap.t * example list * goal option

and circuit =
  | Circuit of string * primitive * circuit SMap.t

let rec equal_type t1 t2 = match (t1, t2) with
  | TNamedTuple m1, TNamedTuple m2 -> begin
    SMap.cardinal m1 = SMap.cardinal m2 && (SMap.fold (fun name t1 b ->
      if b then match SMap.find_opt name m2 with
        | Some t2 -> equal_type t1 t2
        | None -> false
      else false
    ) m1 true)
  end
  | TBool, TBool -> true
  | _ -> false

let rec ty_of_const = function
  | CBool _ -> TBool
  | CNamedTuple m -> TNamedTuple (SMap.map ty_of_const m)

let rec ty_to_string = function
  | TBool -> "bool"
  | TNamedTuple t -> begin
    let rec aux = function
      | [] -> "}"
      | (x, y) :: [] -> x ^ " : " ^ ty_to_string y ^ "}"
      | (x, y) :: q  -> x ^ " : " ^ ty_to_string y ^ "; " ^ aux q
    in

    "{" ^ aux (SMap.bindings t)
  end

let rec const_to_string = function
  | CBool true  -> "true"
  | CBool false -> "false"
  | CNamedTuple m ->
      "{" ^ SMap.fold (fun name c s ->
        name ^ " := " ^ const_to_string c ^ (if String.length s > 1 then "; " ^ s else s)
      ) m "}"

let get_loc () = symbol_start_pos (), symbol_end_pos ()

exception Typing_error of string * position

let construct_expr (loc:position) (env: ty SMap.t) : ((ty SMap.t) -> expr) expr_internal -> expr = function
  | Variable name -> begin
    match SMap.find_opt name env with
    | Some t -> {loc = loc; expr = Variable name; ty = t}
    | None -> raise (Typing_error ("undefined variable `" ^ name ^ "`", loc))
  end
  | NamedTuple tuple -> begin
    let tuple = SMap.map (fun f -> f env) tuple in
    {loc = loc; ty = TNamedTuple (SMap.map (fun e -> e.ty) tuple); expr = NamedTuple tuple}
  end
  | ITE (c, t, e) -> begin
    let c = c env in
    let t = t env in
    let e = e env in
    if not (equal_type c.ty TBool) then
      raise (Typing_error ("expected boolean", c.loc));

    if not (equal_type e.ty t.ty) then
      raise (Typing_error ("the two branch doesn't have the same sort", loc));

    {loc=loc; ty=t.ty; expr = ITE (c, e, t)}
  end
  | Const b -> {loc=loc; ty=TBool; expr = Const b}
  | Unop (Get s, e) -> begin
    let e = e env in
    match e.ty with
    | TNamedTuple ty -> begin
      match SMap.find_opt s ty with
      | Some t -> {loc=loc; ty=t; expr=Unop (Get s, e)}
      | None -> raise (Typing_error ("`" ^ ty_to_string (TNamedTuple ty) ^ "` doesn't have a field `" ^ s ^ "`", loc))
    end
      | TBool -> raise (Typing_error ("Bool != NamedTuple", loc))
  end
  | Unop (Not, e) -> begin
    let e = e env in
    if not (equal_type e.ty TBool) then
      raise (Typing_error ("not is a boolean operation", loc));

    {loc = loc; expr = Unop (Not, e); ty=TBool}
  end
  | LetIn (x, e1, e2) -> begin
    let e1 = e1 env in
    let e2 = e2 (SMap.add x e1.ty env) in

    {loc=loc; expr=LetIn (x, e1, e2); ty=e2.ty}
  end
  | Binop (e1, Xor, e2) -> begin
    let e1 = e1 env in
    let e2 = e2 env in

    if not (equal_type e1.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e1.ty ^ "` is different to `Bool`", e1.loc));

    if not (equal_type e2.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e2.ty ^ "` is different to `Bool`", e2.loc));

    {ty=TBool; loc=loc; expr = Binop (e1, Xor, e2)}
  end
  | Binop (e1, And, e2) -> begin
    let e1 = e1 env in
    let e2 = e2 env in

    if not (equal_type e1.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e1.ty ^ "` is different to `Bool`", e1.loc));

    if not (equal_type e2.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e2.ty ^ "` is different to `Bool`", e2.loc));

    {ty=TBool; loc=loc; expr = Binop (e1, And, e2)}
  end
  | Binop (e1, Or, e2) -> begin
    let e1 = e1 env in
    let e2 = e2 env in

    if not (equal_type e1.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e1.ty ^ "` is different to `Bool`", e1.loc));

    if not (equal_type e2.ty TBool) then
      raise (Typing_error ("`" ^ ty_to_string e2.ty ^ "` is different to `Bool`", e2.loc));

    {ty=TBool; loc=loc; expr = Binop (e1, Or, e2)}
  end
  | Binop (e1, Eq, e2) -> begin
    let e1 = e1 env in
    let e2 = e2 env in

    if not (equal_type e1.ty e2.ty) then
      raise (Typing_error ("`" ^ ty_to_string e1.ty ^ "` is different to `" ^ ty_to_string e2.ty ^ "`", loc));

    {ty=TBool; loc=loc; expr = Binop (e1, Eq, e2)}
  end
