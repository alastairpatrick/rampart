%{
open Ast
let nop_stat = { u = Compound []; loc = Location.null_location }
%}

%token<string> ID
%token<int64> UINT_LIT

(* Keep in alphabetic order, grouped by first letter *)
%token ARROW
%token BOOL
%token COLON COMMA
%token ELSE EOF EOL EQUALS
%token FALSE
%token FUN
%token IF IN INT
%token LCURLY LET LPAREN
%token MINUS MINUS_EQUALS MUT
%token OVER OVER_EQUALS
%token PLUS PLUS_EQUALS
%token RCURLY RPAREN
%token TIMES TIMES_EQUALS TRUE

%right IN
%right EQUALS TIMES_EQUALS PLUS_EQUALS OVER_EQUALS MINUS_EQUALS
%nonassoc COLON
%nonassoc ARROW
%left MINUS PLUS
%left OVER TIMES
%right UNARY
%right LPAREN
 
%type<file> main
%type<expr_variant> expr_variant
%type<expr> expr
%type<stat_variant> stat_variant
%type<stat> stat

%start main

%%

%inline comma
  : COMMA EOL*                                      {}

%inline lparen
  : LPAREN EOL*                                     {}

%inline rparen
  : RPAREN                                          {}

typ
  : BOOL                                            { BoolT }
  | INT                                             { IntT 64 }
  | lparen ts=separated_list(comma, typ) rparen     { match ts with [singleton] -> singleton | _ -> TupleT ts }

%inline bin_op
  : PLUS                                            { Add }
  | MINUS                                           { Subtract }
  | TIMES                                           { Multiply }
  | OVER                                            { Divide }

un_op
  : MINUS                                           { Negate }

%inline assignment_op
  : PLUS_EQUALS                                     { Some Add }
  | MINUS_EQUALS                                    { Some Subtract }
  | TIMES_EQUALS                                    { Some Multiply }
  | OVER_EQUALS                                     { Some Divide }
  | EQUALS                                          { None }

stat_seq
  : ss=list(terminated(stat, EOL+))                 { ss }

compound
  : LCURLY RCURLY                                   { Compound [] }
  | LCURLY EOL+ ss=stat_seq RCURLY                  { Compound ss }

param
  : id=ID COLON t=typ                               { ($loc, id, t) }

func_body
  : b=compound_stat                                 { b }
  | ARROW b=expr                                    { {u = Compound [{u = Expr b; loc = $loc}]; loc = $loc} }

return_type
  : COLON t=typ                                     { t }

func
  : lparen params=separated_list(comma, param)
    rparen return_type=return_type? EOL*
    body=func_body                                  { Function (params, return_type, body) }

%inline expr_variant
  : n=UINT_LIT                                      { Int n }
  | FALSE                                           { Bool false }
  | TRUE                                            { Bool true }
  | id=ID                                           { Identifier id }
  | lparen es=separated_list(comma, expr) rparen    { match es with [{u=singleton; _}] -> singleton | _ -> Tuple es }
  | a=expr op=bin_op EOL* b=expr                    { BinOp (op, a, b) }
  | op=un_op e=expr %prec UNARY                     { UnOp (op, e) }
  | LET id=ID                                       { Let (id, false) }
  | MUT id=ID                                       { Let (id, true) }
  | e=expr COLON t=typ                              { Convert (e, t) }
  | a=expr IN EOL* b=expr                           { In (a, b) }
  | a=expr op=assignment_op EOL* b=expr             { Assignment (op, a, b) }
  | FUN f=func                                      { f }
  | f=expr lparen
    args=separated_list(comma, expr) rparen         { Call (f, args) }

expr
  : e=expr_variant                                  { {typ = void_type; loc = $loc; u = e} }

%inline stat_variant
  : FUN id=ID f=func                                { Expr {
                                                      u = Assignment (None, {typ = void_type; loc = $loc; u = Let (id, false)}, {typ = void_type; loc = $loc; u = f});
                                                      typ = void_type;
                                                      loc = $loc
                                                    } }
  | e=expr                                          { Expr e }
  | s=compound                                      { s }
  | IF condition=expr EOL* consequent=compound_stat { Conditional (condition, consequent, nop_stat) }
  | IF condition=expr EOL* consequent=compound_stat
    EOL* ELSE EOL* alternative=compound_stat        { Conditional (condition, consequent, alternative) }

%inline stat
  : s=stat_variant                                  { {u=s; loc = $loc} }

compound_stat
  : s=compound                                      { {u=s; loc = $loc} }

main_seq
  : h=stat EOL+ t=main_seq                          { h :: t }
  | s=stat EOL* EOF                                 { [s] }

main
  : EOL* EOF                                        { [] }
  | EOL* ss=main_seq                                { ss }
  