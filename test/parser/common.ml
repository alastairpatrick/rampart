open Rampart

let parse text =
  let diagnostic = Diagnostic.output_diagnostic (Diagnostic.make_diagnostic_sink ()) in
  Lexing.from_string (text)
  |> Rampart.Parser.main (Rampart.Lexer.token diagnostic)
  |> Ast.show_file
  |> print_endline