open Rampart

let bind text =
  let diagnostic = Diagnostic.output_diagnostic (Diagnostic.make_diagnostic_sink ()) in
  let env = Rampart.Bind.top_scope diagnostic in
  Lexing.from_string (text)
  |> Rampart.Parser.main (Rampart.Lexer.token diagnostic)
  |> Rampart.Bind.bind_statements env
  |> snd
  |> Ast.show_file
  |> print_endline