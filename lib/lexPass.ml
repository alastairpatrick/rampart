type ltoken = Parser.token * Lexing.position * Lexing.position

let next_token_unpure (lexbuf: Lexing.lexbuf): ltoken =
  let token = Lexer.token lexbuf in
  (* Printf.printf "'%s' %d %d\n" (Lexing.lexeme lexbuf) (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf); *)
  token, (Lexing.lexeme_start_p lexbuf), (Lexing.lexeme_end_p lexbuf)

let rec lex_pass (lexbuf: Lexing.lexbuf) : ltoken list =
  let token = next_token_unpure lexbuf in
  match token with
    | Parser.EOF, _, _ -> [token]
    | token -> token :: (lex_pass lexbuf)
