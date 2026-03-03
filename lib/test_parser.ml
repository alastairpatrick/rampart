open Diagnostic
open LexPass
open Recovery

let parse text =
  let lexbuf = Lexing.from_string text in
  let tokens = lex_pass lexbuf in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    (* let stats = Parser.main Lexer.token lexbuf in *)
    Sexplib.Sexp.output_hum stdout (Ast.sexp_of_statement statement)

(* Expressions *)

let%expect_test _ =
  parse "true;";
  [% expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  parse "false;";
  [% expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  parse "1+1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "1 - 1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Minus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "x * 2;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Times (@1 (Identifier x)) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  parse "n == 0;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Equals (@1 (Identifier n)) (@1 (IntLiteral 0)))))))))
    |}]

let%expect_test _ =
  parse "n != 1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp NotEquals (@1 (Identifier n)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "a / 1 + 3;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (BinaryOp Plus
           (@1 (BinaryOp Div (@1 (Identifier a)) (@1 (IntLiteral 1))))
           (@1 (IntLiteral 3)))))))))
    |}]

let%expect_test _ =
  parse "3 + a / 1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (BinaryOp Plus (@1 (IntLiteral 3))
           (@1 (BinaryOp Div (@1 (Identifier a)) (@1 (IntLiteral 1)))))))))))
    |}]

let%expect_test _ =
  parse "a / (1+3);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (BinaryOp Div (@1 (Identifier a))
           (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 3)))))))))))
    |}]

let%expect_test _ =
  parse "-x;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (UnaryOp Minus (@1 (Identifier x)))))))))
    |}]

let%expect_test _ =
  parse "a == 0 ? 1 : 2;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Conditional
           (@1 (BinaryOp Equals (@1 (Identifier a)) (@1 (IntLiteral 0))))
           (@1 (IntLiteral 1)) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  parse "();";
  [% expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (Tuple ()))))))) |}]

let%expect_test _ =
  parse "(1, 2);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))
    |}]

let%expect_test _ =
  parse "typeof(x);";
  [% expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (TypeOf (@1 (Identifier x))))))))) |}]

let%expect_test _ =
  parse "arity(x);";
  [% expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (Arity (@1 (Identifier x))))))))) |}]

let%expect_test _ =
  parse "int (int, bool);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (Call (@1 (Type Int)) ((@1 (Type Int)) (@1 (Type Bool))) false)))))))
    |}]

let%expect_test _ =
  parse "int(int) pure;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Call (@1 (Type Int)) ((@1 (Type Int))) true)))))))
    |}]

    (* Declarations *)

let%expect_test _ =
  parse "int x;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x) (init_expr ())))))))
    |}]

let%expect_test _ =
  parse "int x = 2+1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr
           ((@1 (BinaryOp Plus (@1 (IntLiteral 2)) (@1 (IntLiteral 1))))))))))))
    |}]

let%expect_test _ =
  parse "mut int x;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ())))))))
    |}]

let%expect_test _ =
  parse "let max = 5;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (Assignment (@1 (Let (Identifier max))) (@1 (IntLiteral 5)))))))))
    |}]

let%expect_test _ =
  parse "int max(int a, int b) { a > b ? a : b; }";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ()) (type_expr ()) (name max)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
                  (init_expr ())))))
              ()
              (@1
               (Compound
                ((@1
                  (Expression
                   (@1
                    (Conditional
                     (@1
                      (BinaryOp Greater (@1 (Identifier a)) (@1 (Identifier b))))
                     (@1 (Identifier a)) (@1 (Identifier b)))))))))))))))))))
    |}]
 
let%expect_test _ =
  parse "let _ = 7;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Assignment (@1 (Let Any)) (@1 (IntLiteral 7)))))))))
    |}]

    
let%expect_test _ =
  parse "_=7;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Assignment (@1 (Let Any)) (@1 (IntLiteral 7)))))))))
    |}]

let%expect_test _ =
  parse "(let a, let b) = (1, 2);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment
           (@1 (Tuple ((@1 (Let (Identifier a))) (@1 (Let (Identifier b))))))
           (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
    |}]

let%expect_test _ =
  parse "(int, int) x = (1, 2);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ())
          (type_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))) (name x)
          (init_expr ((@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2)))))))))))))
    |}]

let%expect_test _ =
  parse "let a = 1 in a + 1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (In (@1 (Assignment (@1 (Let (Identifier a))) (@1 (IntLiteral 1))))
           (@1 (BinaryOp Plus (@1 (Identifier a)) (@1 (IntLiteral 1)))))))))))
    |}]

  (* Lambdas & calls *)

let%expect_test _ =
  parse "lambda (a, b) {};";
  [% expect{|
    Error line 1, characters 1-6: unexpected 'lambda' keyword
    Error line 1, character 16: unexpected '}' symbol
    (@1 (OrderIndependent ()))
    |}]

let%expect_test _ =
  parse "int lambda() {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Lambda (@1 (Type Int)) () () (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int lambda() pure {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (Lambda (@1 (Type Int)) () ((pure)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int lambda() const {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (Lambda (@1 (Type Int)) () ((const)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "lambda (int a, int b) {};";
  [% expect{|
    Error line 1, characters 1-6: unexpected 'lambda' keyword
    Error line 1, character 24: unexpected '}' symbol
    (@1 (OrderIndependent ()))
    |}]

let%expect_test _ =
  parse "int lambda (int a, int b) {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Lambda (@1 (Type Int))
           ((@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
               (init_expr ())))))
           () (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int lambda (int a, int b) pure {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Lambda (@1 (Type Int))
           ((@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
               (init_expr ())))))
           ((pure)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int lambda (int a, int b) const {};";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Lambda (@1 (Type Int))
           ((@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
               (init_expr ())))))
           ((const)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int foo (int a, int b) {}";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ()) (type_expr ()) (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
                  (init_expr ())))))
              () (@1 (Compound ()))))))))))))
    |}]

let%expect_test _ =
  parse "int foo (int a, int b) pure {}";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Declaration
         ((modifiers ()) (type_expr ()) (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
                  (init_expr ())))))
              ((pure)) (@1 (Compound ()))))))))))))
    |}]


let%expect_test _ =
  parse "foo();";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (Call (@1 (Identifier foo)) () false)))))))
    |}]

let%expect_test _ =
  parse "foo(7);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (Call (@1 (Identifier foo)) ((@1 (IntLiteral 7))) false)))))))
    |}]

let%expect_test _ =
  parse "return;";
  [% expect{| (@1 (OrderIndependent ((@1 (Return ()))))) |}]

let%expect_test _ =
  parse "return 7;";
  [% expect{| (@1 (OrderIndependent ((@1 (Return ((@1 (IntLiteral 7)))))))) |}]


  (* Control flow Statements *)

let%expect_test _ =
  parse "if condition {}";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (If (@1 (Identifier condition)) (@1 (Compound ())) (@1 (Compound ())))))))
    |}]

let%expect_test _ =
  parse "if condition {} else {}";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (If (@1 (Identifier condition)) (@1 (Compound ())) (@1 (Compound ())))))))
    |}]
   

(* End of line skipping *)

let%expect_test _ =
  parse "1\n-1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (IntLiteral 1))))
       (@1 (Expression (@1 (UnaryOp Minus (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "1-\n1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Minus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse {|
    if c {
    }
    1
  |};
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (If (@1 (Identifier c)) (@1 (Compound ())) (@1 (Compound ()))))
       (@1 (Expression (@1 (IntLiteral 1)))))))
    |}]

let%expect_test _ =
  parse {|
    if c
    {
    }
    1
  |};
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (If (@1 (Identifier c)) (@1 (Compound ())) (@1 (Compound ()))))
       (@1 (Expression (@1 (IntLiteral 1)))))))
    |}]

let%expect_test _ =
  parse {|
    if c
    {
    }
    else
    {
    }
    1
  |};
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (If (@1 (Identifier c)) (@1 (Compound ())) (@1 (Compound ()))))
       (@1 (Expression (@1 (IntLiteral 1)))))))
    |}]

let%expect_test _ =
  parse {|
    if c {
    }
    else {
    }
    1
  |};
  [% expect{|
    (@1
     (OrderIndependent
      ((@1 (If (@1 (Identifier c)) (@1 (Compound ())) (@1 (Compound ()))))
       (@1 (Expression (@1 (IntLiteral 1)))))))
    |}]

(* ERRORS *)

  
let%expect_test _ =
  parse "+; 1+1;";
  [% expect{|
    Error line 1, character 1: unexpected '+' symbol
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "1+; 1+1;";
  [% expect{|
    Error line 1, character 3: unexpected ';' symbol
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "(1; 1+1;";
  [% expect{|
    Error line 1, character 3: unexpected ';' symbol
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "1); 1+1;";
  [% expect{|
    Error line 1, character 2: unexpected ')' symbol
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse "{a}";
  [% expect{|
    Error line 1, character 3: unexpected '}' symbol
    (@1 (OrderIndependent ((@1 (Compound ())))))
    |}]

