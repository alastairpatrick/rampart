open Rampart

let evaluate text =
  let diagnostic = Diagnostic.output_diagnostic (Diagnostic.make_diagnostic_sink ()) in
  Lexing.from_string (text)
  |> Rampart.Parser.main (Rampart.Lexer.token diagnostic)
  |> Rampart.Evaluate.evaluate ()
  |> Ast.show_file
  |> print_endline