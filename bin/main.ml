open Rampart.Ast
open Rampart.Bind
open Rampart.Diagnostic
open Rampart.Error
open Rampart.LexPass
open Rampart.Recovery
open Printf

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let tokens = lex_pass lexbuf in
    let env = top_scope () in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    let _, statement = bind_program env (statement) in
    Sexplib.Sexp.output_hum stdout (sexp_of_statement statement)

  with
  | Located_error (_, message) -> printf "Error: %s" message
  | e -> print_endline (Printexc.to_string e)
