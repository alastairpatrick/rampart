/* File parser.mly */
%{
    open Ast
    open Location
    open ParserLowering
    let loc ((s: Lexing.position), (e: Lexing.position)) : location = make_location s e
%}
%token <string> ID
%token <int> INT_LIT

(* Please keep these in alphabetic order *)
%token AMPERSAND ANY ARITY ASSIGN
%token BACKSLASH BANG BOOL
%token CARET CASE COLON COMMA CONST
%token DIV DO
%token ELSE EOF EOL EQUALS
%token FALSE FOR
%token GREATER GREATER_EQUALS
%token IF IN INT
%token LBRACKET LESS LESS_EQUALS LCURLY LET LOGICAL_AND LOGICAL_OR LPAREN
%token SHIFT_LEFT SHIFT_RIGHT
%token MINUS MODULO MUT
%token NOT_EQUALS
%token PIPE PLUS PURE
%token QUESTION
%token RARROW RBRACKET RETURN RCURLY RPAREN
%token SEMI SWITCH
%token TILDE TIMES TRUE TYPE TYPEOF
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

lambda_modifiers
  : /* empty */                             { empty_lambda_modifiers }
  | lambda_modifiers PURE                   { { $1 with pure = true } }
  | lambda_modifiers CONST                  { { $1 with const = true } }
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
  | LBRACKET es=exprs0 RBRACKET                             { loc $loc, DynamicArrayLiteral (Array.of_list es, None) }
  | TYPEOF LPAREN e=expr RPAREN                             { loc $loc, TypeOf e }
  | ARITY LPAREN e=expr RPAREN                              { loc $loc, Arity e }
  ;

postfix_expr
  : e=primary_expr                                          { e }
  | f=postfix_expr LPAREN es=exprs0 RPAREN
    lm=lambda_modifiers                                     { loc $loc, Call (f, es, lm) }
  | a=postfix_expr LBRACKET e=expr? RBRACKET                 { loc $loc, Index (a, e) }
  ;

unary_expr
  : e=postfix_expr                                          { e }
  | MINUS e=postfix_expr                                    { loc $loc, UnaryOp (Negate, e) }
  | BANG e=postfix_expr                                     { loc $loc, UnaryOp (LogicalNot, e) }
  | TILDE e=postfix_expr                                    { loc $loc, UnaryOp (BitwiseInvert, e) }
  ;

multiplicative_expr
  : e=unary_expr                                            { e }
  | a=multiplicative_expr TIMES b=unary_expr                { loc $loc, BinaryOp (Times, a, b) }
  | a=multiplicative_expr DIV b=unary_expr                  { loc $loc, BinaryOp (Div, a, b) }
  | a=multiplicative_expr MODULO b=unary_expr               { loc $loc, BinaryOp (Modulo, a, b) }
  ;

additive_expr
  : e = multiplicative_expr                                 { e }
  | a=additive_expr PLUS b=multiplicative_expr              { loc $loc, BinaryOp (Plus, a, b) }
  | a=additive_expr MINUS b=multiplicative_expr             { loc $loc, BinaryOp (Minus, a, b) }
  ;

shift_expr
  : e = additive_expr                                       { e }
  | a=shift_expr SHIFT_LEFT b=additive_expr                 { loc $loc, BinaryOp (ShiftLeft, a, b) }
  | a=shift_expr SHIFT_RIGHT b=additive_expr                { loc $loc, BinaryOp (ShiftRight, a, b) }
  ;

relational_expr
  : e=shift_expr                                            { e }
  | a=relational_expr LESS b=shift_expr                    { loc $loc, BinaryOp (Less, a, b) }
  | a=relational_expr LESS_EQUALS b=shift_expr             { loc $loc, BinaryOp (LessEquals, a, b) }
  | a=relational_expr GREATER b=shift_expr                 { loc $loc, BinaryOp (Greater, a, b) }
  | a=relational_expr GREATER_EQUALS b=shift_expr          { loc $loc, BinaryOp (GreaterEquals, a, b) }
;

equality_expr
  : e=relational_expr                                       { e }
  | a=equality_expr EQUALS b=relational_expr                { loc $loc, BinaryOp (Equals, a, b) }
  | a=equality_expr NOT_EQUALS b=relational_expr            { loc $loc, BinaryOp (NotEquals, a, b) }
  ;

bitwise_and_expr
  : e=equality_expr                                         { e }
  | a=bitwise_and_expr AMPERSAND b=equality_expr            { loc $loc, BinaryOp (BitwiseAnd, a, b) }
  ;

bitwise_xor_expr
  : e=bitwise_and_expr                                      { e }
  | a=bitwise_xor_expr CARET b=bitwise_and_expr             { loc $loc, BinaryOp (BitwiseXor, a, b) }
  ;

bitwise_or_expr
  : e=bitwise_xor_expr                                      { e }
  | a=bitwise_or_expr PIPE b=bitwise_xor_expr               { loc $loc, BinaryOp (BitwiseOr, a, b) }
  ;

logical_and_expr
  : e=bitwise_or_expr                                       { e }
  | a=logical_and_expr LOGICAL_AND b=bitwise_or_expr        { loc $loc, BinaryOp (LogicalAnd, a, b) }
  ;

logical_or_expr
  : e=logical_and_expr                                      { e }
  | a=logical_or_expr LOGICAL_OR b=logical_and_expr         { loc $loc, BinaryOp (LogicalOr, a, b) }
  ;

binary_expr: e=logical_or_expr {e}

conditional_expr
  : e=binary_expr                                           { e }
  | c=binary_expr QUESTION a=expr COLON b=conditional_expr  { loc $loc, Conditional (c, a, b) }
  ;

assign_expr
  : e = conditional_expr                                    { e }
  | a=postfix_expr ASSIGN b=assign_expr                     { loc $loc, Assignment (a, b) }
  ;

in_expr
  : a=assign_expr IN b=in_expr                              { loc $loc, In (a, b) }
  | e=assign_expr                                           { e }
  ;

lambda_body
  : b=compound_stat                                         { b }
  | RARROW e=in_expr                                        { loc $loc, Return e }
  ;

lambda_expr
  : e=in_expr                                               { e }
  | BACKSLASH rt=primary_expr LPAREN ps=params0 RPAREN
    lm=lambda_modifiers b=lambda_body                       { loc $loc, Lambda (rt, ps, lm, b, None) }
  ;

expr: e=lambda_expr                                         { e }

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
  | t=expr n=ID LPAREN ps=params0 RPAREN
    lm=lambda_modifiers b=compound_stat                         { {modifiers=empty_declaration_modifiers; type_expr=None; name=n; init_expr=Some (loc $loc, Lambda (t, ps, lm, b, None)) } }
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
  | RETURN e=expr semi                                          { loc $loc, Return e }
  | RETURN semi                                                 { loc $loc, Return (loc $loc, Tuple []) }
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
