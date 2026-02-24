{
open Parser
exception UnexpectedChar of char
}

let id_first = ['A'-'Z' 'a'-'z']
let id_subs = ['A'-'Z' 'a'-'z' '0'-'9' '_']

rule token = parse
    [' ' '\t'     ]                     { token lexbuf }     (* skip blanks *)
    | '\n'                              { EOL }
    | "bool"                            { BOOL }
    | "case"                            { CASE }
    | "do"                              { DO }
    | "else"                            { ELSE }
    | "false"                           { FALSE }
    | "for"                             { FOR }
    | "if"                              { IF }
    | "in"                              { IN }
    | "int"                             { INT }
    | "lambda"                          { LAMBDA }
    | "let"                             { LET }
    | "return"                          { RETURN }
    | "switch"                          { SWITCH }
    | "true"                            { TRUE }
    | "typeof"                          { TYPEOF }
    | "void"                            { VOID }
    | "while"                           { WHILE }
    | (id_first id_subs*) as lxm        { ID(lxm) }
    | ['0'-'9']+ as lxm                 { INT_LIT(int_of_string lxm) }
    | "=="                              { EQUALS }
    | "!="                              { NOT_EQUALS }
    | "<-"                              { LARROW }
    | "->"                              { RARROW }
    | '='                               { ASSIGN }
    | '+'                               { PLUS }
    | '-'                               { MINUS }
    | '*'                               { TIMES }
    | '/'                               { DIV }
    | '?'                               { QUESTION }
    | ':'                               { COLON }
    | '('                               { LPAREN }
    | ')'                               { RPAREN }
    | '{'                               { LCURLY }
    | '}'                               { RCURLY }
    | '<'                               { LESS }
    | '>'                               { GREATER }
    | ';'                               { SEMI }
    | ','                               { COMMA }
    | '_'                               { ANY }
    | _ as lxm                          { raise (UnexpectedChar lxm)  }
    | eof                               { EOF }
