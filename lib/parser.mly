/* File parser.mly */
%{
    open Ast
    open Location
    open Prelower
    let loc ((s: Lexing.position), (e: Lexing.position)) : location = make_location s e
%}
%token <string> ID
%token <int> INT_LIT

%token ANY ARITY ASSIGN
%token BOOL
%token CASE COLON COMMA
%token DIV DO
%token ELSE EOF EOL EQUALS
%token FALSE FOR
%token GREATER
%token IF IN INT
%token LAMBDA LARROW LESS LCURLY LET LPAREN
%token MINUS MUT
%token NOT_EQUALS
%token PLUS PURE
%token QUESTION
%token RARROW RETURN RINEQ RCURLY RPAREN
%token SEMI SWITCH
%token TIMES TRUE TYPE TYPEOF
%token VOID
%token WHILE

%start main             /* the entry point */

%type <statement> main
%type <switch_case> switch_case
%type <expression> expr
%type <statement> compound_stat

%%

param
  : t=expr n=ID                             { loc $loc, Declaration {modifiers=empty_declaration_modifiers; type_expr=Some t; name=n; init_expr=None} }
  ;

params0 : es=separated_list(COMMA, param)   { es };

pattern
  : n=ID                                    { Identifier n }
  | ANY                                     { Any }
  ;

primary_expr
  : VOID                                                    { loc $loc, Type Void }                     
  | INT                                                     { loc $loc, Type Int }
  | BOOL                                                    { loc $loc, Type Bool }
  | TYPE                                                    { loc $loc, Type Type }
  | v=INT_LIT                                               { loc $loc, IntLiteral v }
  | TRUE                                                    { loc $loc, BoolLiteral true }
  | FALSE                                                   { loc $loc, BoolLiteral false }
  | n=ID                                                    { loc $loc, Identifier n }
  | LET p=pattern                                           { loc $loc, Let p }
  | ANY                                                     { loc $loc, Let Any }
  | LPAREN es=exprs0 RPAREN                                 { make_tuple_node (loc $loc) es }
  | f=primary_expr LPAREN es=exprs0 RPAREN                  { loc $loc, Call (f, es, false) }
  | f=primary_expr LPAREN es=exprs0 RPAREN PURE             { loc $loc, Call (f, es, true) }
  | f=primary_expr LAMBDA LPAREN ps=params0 RPAREN
    b=compound_stat                                         { loc $loc, Lambda (f, ps, empty_lambda_modifiers, b) }
  | f=primary_expr LAMBDA LPAREN ps=params0 RPAREN PURE
    b=compound_stat                                         { loc $loc, Lambda (f, ps, { pure = true }, b) }
  | TYPEOF LPAREN e=expr RPAREN                             { loc $loc, TypeOf e }
  | ARITY LPAREN e=expr RPAREN                              { loc $loc, Arity e }
  ;

unary_expr
  : e=primary_expr                                          { e }
  | MINUS e=unary_expr                                      { loc $loc, UnaryOp (Minus, e) }
  ;

multiplicative_expr
  : e=unary_expr                                            { e }
  | a=multiplicative_expr TIMES b=unary_expr                { loc $loc, BinaryOp (Times, a, b) }
  | a=multiplicative_expr DIV b=unary_expr                  { loc $loc, BinaryOp (Div, a, b) }
  ;

additive_expr
  : e = multiplicative_expr                                 { e }
  | a=additive_expr PLUS b=multiplicative_expr              { loc $loc, BinaryOp (Plus, a, b) }
  | a=additive_expr MINUS b=multiplicative_expr             { loc $loc, BinaryOp (Minus, a, b) }
  ;

relational_expr
  : e=additive_expr                                         { e }
  | a=relational_expr LESS b=additive_expr                  { loc $loc, BinaryOp (Less, a, b) }
  | a=relational_expr GREATER b=additive_expr               { loc $loc, BinaryOp (Greater, a, b) }

equality_expr
  : e=relational_expr                                       { e }
  | a=equality_expr EQUALS b=relational_expr                { loc $loc, BinaryOp (Equals, a, b) }
  | a=equality_expr NOT_EQUALS b=relational_expr            { loc $loc, BinaryOp (NotEquals, a, b) }
  ;

binary_expr: e=equality_expr {e}

conditional_expr
  : e=binary_expr                                           { e }
  | c=binary_expr QUESTION a=expr COLON b=conditional_expr  { loc $loc, Conditional (c, a, b) }
  ;

assign_expr
  : e = conditional_expr                                    { e }
  | a=primary_expr ASSIGN b=assign_expr                     { loc $loc, Assignment (a, b) }
  ;

in_expr
  : a=assign_expr IN b=in_expr                              { loc $loc, In (a, b) }
  | e=assign_expr                                           { e }
  ;

expr: e=in_expr                             { e }

exprs0 : es=separated_list(COMMA, expr)     { es };

semi
  : SEMI                                    { () }
  | EOL                                     { () }
  ;

else_clause
  : ELSE b=compound_stat                    { b }
  ;

initialize
  : ASSIGN v=expr                           { v }
  ;

switch_case_if
  : IF e=expr                               { e }
  ;

switch_case
  : CASE p=expr e=switch_case_if? b=compound_stat { loc $loc, Some p, e, b }
  | ELSE e=switch_case_if? b=compound_stat        { loc $loc, None, e, b }
  ;

declaration
  : t=expr n=ID v=initialize? semi
                                                                { {modifiers=empty_declaration_modifiers; type_expr=Some t; name=n; init_expr=v} }
  | t=expr n=ID LPAREN ps=params0 RPAREN b=compound_stat        { {modifiers=empty_declaration_modifiers; type_expr=None; name=n; init_expr=Some (loc $loc, Lambda (t, ps, empty_lambda_modifiers, b)) } }
  | t=expr n=ID LPAREN ps=params0 RPAREN PURE b=compound_stat   { {modifiers=empty_declaration_modifiers; type_expr=None; name=n; init_expr=Some (loc $loc, Lambda (t, ps, { pure = true }, b)) } }
  | MUT d=declaration                                           { let new_modifiers = { mut=true } in { d with modifiers = new_modifiers } }
  ;

stat
  : e=expr semi                                                 { loc $loc, Expression e }
  | SWITCH e=expr cs=switch_case+                               { loc $loc, Switch (e, cs) }
  | d=declaration                                               { loc $loc, Declaration d }
  | s=compound_stat                                             { s }
  | IF c=expr a=compound_stat b=else_clause?                    { prelower_if (loc($loc)) c a b }
  | FOR i=stat c=expr semi n=expr b=compound_stat               { prelower_for (loc($loc)) i c n b }
  | FOR LPAREN i=stat c=expr semi n=expr RPAREN b=compound_stat { prelower_for (loc($loc)) i c n b }
  | WHILE c=expr b=compound_stat                                { prelower_while (loc($loc)) c b }
  | DO b=compound_stat WHILE c=expr semi                        { loc $loc, DoWhile (b, c) }
  | RETURN e=expr? semi                                         { loc $loc, Return e }
  ;

stats0
  : ss=list(stat) { ss }
  ;

expect_stat
  : /* empty */                             { () }
  ;

compound_stats
  : LCURLY expect_stat ss=stats0 RCURLY     { ss }
  ;

compound_stat
  : ss=compound_stats                       { (loc $loc, Compound ss) }
  ;

main
  : ss=stats0 EOF                           { (loc $loc, OrderIndependent ss) }
  ;
