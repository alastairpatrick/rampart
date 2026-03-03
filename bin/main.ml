open Hello.Ast
open Hello.Bind
open Hello.Diagnostic
open Hello.Error
open Hello.Const_eval
open Hello.LexPass
open Hello.Recovery
open Printf

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let tokens = lex_pass lexbuf in
    let env = top_scope () in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    let num_variables, statement = bind_program env (statement) in
    let global_frame = make_global_frame num_variables in
    let program = evaluate_statement env global_frame Search_for_declaration_types statement in
    Sexplib.Sexp.output_hum stdout (sexp_of_statement program)

  with
  | Located_error (_, message) -> printf "Error: %s" message
  | e -> print_endline (Printexc.to_string e)
