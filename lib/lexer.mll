{
open Location
open Parser
}

let id_first = ['A'-'Z' 'a'-'z']
let id_subs = ['A'-'Z' 'a'-'z' '0'-'9' '_']
let space = [' ' '\t']
let newline = '\r'? '\n'

rule token diagnostic = parse
    space+
  | "//" [^'\n']*                     { token diagnostic lexbuf }
  | "/*"                              { skip diagnostic 1 false lexbuf }
  | '\\' newline                      { Lexing.new_line lexbuf; token diagnostic lexbuf }
  | newline                           { Lexing.new_line lexbuf; EOL }

  | "bool"                            { BOOL }
  | "else"                            { ELSE }
  | "false"                           { FALSE }
  | "fun"                             { FUN }
  | "if"                              { IF }
  | "in"                              { IN }
  | "int"                             { INT }
  | "let"                             { LET }
  | "mut"                             { MUT }
  | "true"                            { TRUE }

  | (id_first id_subs*) as lxm        { ID(lxm) }

  | ['0'-'9']+ as lxm
  | '0' ['x' 'X'] ['0'-'9' 'a'-'f' 'A'-'F']+ as lxm
  | '0' ['o' 'O'] ['0'-'7']+ as lxm
  | '0' ['b' 'B'] ['0'-'1']+ as lxm   { UINT_LIT (Int64.of_string lxm) }                                        

  | "->"                              { ARROW }
  | "+="                              { PLUS_EQUALS }
  | "-="                              { MINUS_EQUALS }
  | "*="                              { TIMES_EQUALS }
  | "/="                              { OVER_EQUALS }

  | ':'                               { COLON }
  | ','                               { COMMA }
  | '='                               { EQUALS }
  | '{'                               { LCURLY }
  | '('                               { LPAREN }
  | '-'                               { MINUS }
  | '/'                               { OVER }
  | '+'                               { PLUS }
  | '}'                               { RCURLY }
  | ')'                               { RPAREN }
  | '*'                               { TIMES }

  | _ as lxm                          {
                                        let location = make_location (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) in 
                                        diagnostic Diagnostic.Error location (Printf.sprintf "unexpected token beginning '%s'" (Char.escaped lxm));
                                        skip diagnostic 0 true lexbuf
                                      }

  | eof                               { EOF }

and skip diagnostic depth recovering = parse
  | "/*"            { skip diagnostic (depth + 1) recovering lexbuf }
  | "*/"            {
                      if depth = 1 && not recovering then
                        token diagnostic lexbuf
                      else
                        skip diagnostic (if depth > 0 then (depth - 1) else 0) recovering lexbuf
                    }
  | '\\' newline    {
                      Lexing.new_line lexbuf;
                      skip diagnostic depth recovering lexbuf
                    }
  | newline         {
                      Lexing.new_line lexbuf;
                      if depth = 0 then
                        EOL
                      else
                        skip diagnostic depth recovering lexbuf
                    }
  | _               { skip diagnostic depth recovering lexbuf }
  | eof             {
                      (if depth > 0 then
                        let location = make_location (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) in
                        diagnostic Diagnostic.Error location "unclosed comment");
                      EOF
                    }