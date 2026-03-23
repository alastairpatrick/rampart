{
  open Parser
  exception UnexpectedChar of char

  let count_eols lexbuf : unit =
    String.iter (fun c -> if c = '\n' then Lexing.new_line lexbuf) (Lexing.lexeme lexbuf)
}


let id_first = ['A'-'Z' 'a'-'z']
let id_subs = ['A'-'Z' 'a'-'z' '0'-'9' '_']
let space = [' ' '\t']*
let skip_eols = [' ' '\t' '\n' '\r']*

rule token = parse
  space                               { token lexbuf }     (* skip blanks *)
  | '\n'                              { count_eols lexbuf; EOL }
  | "arity"                           { ARITY }
  | "band"                            { BITWISE_AND }
  | "bnot"                            { BITWISE_NOT }
  | "bor"                             { BITWISE_OR }
  | "bxor"                            { BITWISE_XOR }
  | "bool"                            { BOOL }
  | "const"                           { CONST }
  | "do"                              { DO }
  | skip_eols "else" skip_eols        { count_eols lexbuf; ELSE }
  | "false"                           { FALSE }
  | "for"                             { FOR }
  | "if"                              { IF }
  | "in"                              { IN }
  | "int"                             { INT }
  | "let"                             { LET }
  | "mut"                             { MUT }
  | "pure"                            { PURE }
  | "return"                          { RETURN }
  | "true"                            { TRUE }
  | "typeof"                          { TYPEOF }
  | "type"                            { TYPE }
  | "void"                            { VOID }
  | "when"                            { WHEN }
  | "while"                           { WHILE }
  | (id_first id_subs*) as lxm        { ID(lxm) }
  | ['0'-'9']+ as lxm                 { INT_LIT(Int64.of_string lxm) }
  | "==" skip_eols                    { count_eols lexbuf; EQUALS }
  | "!=" skip_eols                    { count_eols lexbuf; NOT_EQUALS }
  | "<=" skip_eols                    { count_eols lexbuf; LESS_EQUALS }
  | "<<" skip_eols                    { count_eols lexbuf; SHIFT_LEFT }
  | ">>" skip_eols                    { count_eols lexbuf; SHIFT_RIGHT }
  | ">=" skip_eols                    { count_eols lexbuf; GREATER_EQUALS }
  | "<-" skip_eols                    { count_eols lexbuf; LARROW }
  | "->" skip_eols                    { count_eols lexbuf; RARROW }
  | "&&" skip_eols                    { count_eols lexbuf; LOGICAL_AND }
  | skip_eols "||" skip_eols          { count_eols lexbuf; LOGICAL_OR }
  | '(' skip_eols                     { count_eols lexbuf; LPAREN }
  | skip_eols ')'                     { count_eols lexbuf; RPAREN }
  | '[' skip_eols                     { count_eols lexbuf; LBRACKET }
  | skip_eols ']'                     { count_eols lexbuf; RBRACKET }
  | '{' skip_eols                     { count_eols lexbuf; LCURLY }
  | '}'                               { RCURLY }
  | skip_eols ',' skip_eols           { count_eols lexbuf; COMMA }
  | skip_eols "|" skip_eols           { count_eols lexbuf; PIPE }
  | "!" skip_eols                     { count_eols lexbuf; BANG }
  | "~" skip_eols                     { count_eols lexbuf; TILDE }
  | '=' skip_eols                     { count_eols lexbuf; ASSIGN }
  | '+' skip_eols                     { count_eols lexbuf; PLUS }
  | '-' skip_eols                     { count_eols lexbuf; MINUS }
  | '*' skip_eols                     { count_eols lexbuf; TIMES }
  | "%" skip_eols                     { count_eols lexbuf; MODULO }
  | '/' skip_eols                     { count_eols lexbuf; DIV }
  | '\\' skip_eols                    { count_eols lexbuf; BACKSLASH }
  | '?' skip_eols                     { count_eols lexbuf; QUESTION }
  | ':' skip_eols                     { count_eols lexbuf; COLON }
  | '<' skip_eols                     { count_eols lexbuf; LESS }
  | '>' skip_eols                     { count_eols lexbuf; GREATER }
  | ';'                               { SEMI }
  | '_'                               { ANY }
  | _ as lxm                          { raise (UnexpectedChar lxm)  }
  | eof                               { EOF }
