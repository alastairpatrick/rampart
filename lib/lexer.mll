{
open Parser
exception UnexpectedChar of char
}

let id_first = ['A'-'Z' 'a'-'z']
let id_subs = ['A'-'Z' 'a'-'z' '0'-'9' '_']
let space = [' ' '\t']*
let skip_eols = [' ' '\t' '\n' '\r']*

rule token = parse
    space                               { token lexbuf }     (* skip blanks *)
    | '\n'                              { EOL }
    | "arity"                           { ARITY }
    | "band"                            { BITWISE_AND }
    | "bnot"                            { BITWISE_NOT }
    | "bor"                             { BITWISE_OR }
    | "bxor"                            { BITWISE_XOR }
    | "bool"                            { BOOL }
    | "const"                           { CONST }
    | "do"                              { DO }
    | skip_eols "else" skip_eols        { ELSE }
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
    | "==" skip_eols                    { EQUALS }
    | "!=" skip_eols                    { NOT_EQUALS }
    | "<=" skip_eols                    { LESS_EQUALS }
    | "<<" skip_eols                    { SHIFT_LEFT }
    | ">>" skip_eols                    { SHIFT_RIGHT }
    | ">=" skip_eols                    { GREATER_EQUALS }
    | "->" skip_eols                    { RARROW }
    | "&&" skip_eols                    { LOGICAL_AND }
    | skip_eols "||" skip_eols          { LOGICAL_OR }
    | '(' skip_eols                     { LPAREN }
    | skip_eols ')'                     { RPAREN }
    | '[' skip_eols                     { LBRACKET }
    | skip_eols ']'                     { RBRACKET }
    | '{' skip_eols                     { LCURLY }
    | '}'                               { RCURLY }
    | skip_eols ',' skip_eols           { COMMA }
    | skip_eols "|" skip_eols           { PIPE }
    | "!" skip_eols                     { BANG }
    | "~" skip_eols                     { TILDE }
    | '=' skip_eols                     { ASSIGN }
    | '+' skip_eols                     { PLUS }
    | '-' skip_eols                     { MINUS }
    | '*' skip_eols                     { TIMES }
    | "%" skip_eols                     { MODULO }
    | '/' skip_eols                     { DIV }
    | '\\' skip_eols                    { BACKSLASH }
    | '?' skip_eols                     { QUESTION }
    | ':' skip_eols                     { COLON }
    | '<' skip_eols                     { LESS }
    | '>' skip_eols                     { GREATER }
    | ';'                               { SEMI }
    | '_'                               { ANY }
    | _ as lxm                          { raise (UnexpectedChar lxm)  }
    | eof                               { EOF }
