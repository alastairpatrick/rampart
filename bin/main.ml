open Hello.Bind
open Hello.Diagnostic
open Hello.Error
open Hello.Evaluate
open Hello.LexPass
open Hello.Recovery
open Printf

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    let tokens = lex_pass lexbuf in
    let env = top_scope () in
    let statements = parse_recovering (make_diagnostic_sink ()) tokens in
    let num_variables, statements = bind_program env (statements) in
    let machine = make_machine num_variables in 
    evaluate_program machine statements
  with
  | Located_error (_, message) -> printf "Error: %s" message
  | e -> print_endline (Printexc.to_string e)
