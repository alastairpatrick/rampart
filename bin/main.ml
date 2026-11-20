open Rampart

let _ =
  let diagnostic = Diagnostic.make_diagnostic_sink () |> Diagnostic.output_diagnostic in
  Lexing.from_channel stdin |> Parser.main (Lexer.token diagnostic)
