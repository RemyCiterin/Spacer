open Ps_parser
open Ps_ast
open Lexing
let get_loc lb = (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)
open Dsl_to_chc
let print_loc lb input_file =
  let (start_pos, end_pos) = lb in
	let l_start = start_pos.pos_lnum in
  let l_end   = end_pos.pos_lnum   in
	let c_start = start_pos.pos_cnum - start_pos.pos_bol + 1 in
	let c_end   = end_pos.pos_cnum   - start_pos.pos_bol + 1 in
    if l_start = l_end then
	    Format.printf "File \"%s\", line %d, characters %d-%d:\n" input_file l_start c_start c_end
    else
        Format.printf "File \"%s\", line %d-%d:\n" input_file l_start l_end

let report_loc (b,e) file =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  Format.printf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc


let cfg = [("model", "true"); ("proof", "true")]
let ctx = Z3.mk_context cfg


let _ =
  let file_name  = "./tests/test.dsl" in
    let c = open_in file_name in
    let lb = Lexing.from_channel c in

    try
        let file = Ps_parser.file Ps_lexer.token lb in

        let chc_list = dsl_to_chc 15 file ctx in

        CHC.print_chc_smt2 ctx chc_list;


        let solver = Spacer.initial_chc_solver ctx chc_list in

        let cex = Spacer.model_checking solver in

        if Option.is_none cex then
          Format.printf "no circuit found!\n"
        else begin
          Format.printf "circuit found!\n";
          let cex = Option.get cex in
          let circuit = cex_to_circuit ctx file cex in
          print_circuit circuit;
          Format.printf "\n";
        end;

        match solve_with_goal ctx file 8 with
        | Some circuit -> begin
          print_circuit circuit;
          Format.printf "\n";
        end
        | None -> Format.printf "no circuit found!\n"
        ;


        Format.print_flush ();

        close_in c;
        ()
    with
		| Lexer.Lexical_error s ->
			begin
        print_loc (get_loc lb) file_name;
				Format.printf "%s\n" s;
        failwith "fatal error!";
			end

		| Parsing.Parse_error ->
			begin
        print_loc (get_loc lb) file_name;
				Format.printf "Syntax error\n";
        failwith "fatal error!";
			end
    | Typing_error (s, l) ->
      begin
        print_loc l file_name;
        Format.printf "%s\n" s;
        failwith "fatal error!";
      end
