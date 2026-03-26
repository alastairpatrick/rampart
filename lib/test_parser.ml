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
  [% expect{| (@1 (Order_independent ((@1 (Expression (@1 (Bool_literal true))))))) |}]

let%expect_test _ =
  parse "false;";
  [% expect{| (@1 (Order_independent ((@1 (Expression (@1 (Bool_literal false))))))) |}]

let%expect_test _ =
  parse "1+1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "1 - 1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Minus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "x * 2;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Times (@1 (Identifier x)) (@1 (Int_literal 2)))))))))
    |}]

let%expect_test _ =
  parse "n == 0;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Equals (@1 (Identifier n)) (@1 (Int_literal 0)))))))))
    |}]

let%expect_test _ =
  parse "n != 1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Not_equals (@1 (Identifier n)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "a / 1 + 3;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Binary_op Plus
           (@1 (Binary_op Div (@1 (Identifier a)) (@1 (Int_literal 1))))
           (@1 (Int_literal 3)))))))))
    |}]

let%expect_test _ =
  parse "3 + a / 1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Binary_op Plus (@1 (Int_literal 3))
           (@1 (Binary_op Div (@1 (Identifier a)) (@1 (Int_literal 1)))))))))))
    |}]

let%expect_test _ =
  parse "a / (1+3);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Binary_op Div (@1 (Identifier a))
           (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 3)))))))))))
    |}]

let%expect_test _ =
  parse "-x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Unary_op Negate (@1 (Identifier x)))))))))
    |}]

let%expect_test _ =
  parse "a == 0 ? 1 : 2;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Conditional
           (@1 (Binary_op Equals (@1 (Identifier a)) (@1 (Int_literal 0))))
           (@1 (Int_literal 1)) (@1 (Int_literal 2)))))))))
    |}]

let%expect_test _ =
  parse "();";
  [% expect{| (@1 (Order_independent ((@1 (Expression (@1 (Tuple ()))))))) |}]

let%expect_test _ =
  parse "(1, 2);";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Tuple ((@1 (Int_literal 1)) (@1 (Int_literal 2))))))))))
    |}]

let%expect_test _ =
  parse "typeof(x);";
  [% expect{|
    (@1
     (Order_independent ((@1 (Expression (@1 (Type_of (@1 (Identifier x)))))))))
    |}]

let%expect_test _ =
  parse "arity(x);";
  [% expect{| (@1 (Order_independent ((@1 (Expression (@1 (Arity (@1 (Identifier x))))))))) |}]

let%expect_test _ =
  parse "[1, 2, 3];";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Dynamic_array
           ((@1 (Int_literal 1)) (@1 (Int_literal 2)) (@1 (Int_literal 3)))
           Deduced)))))))
    |}]
let%expect_test _ =
  parse "[int];";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Dynamic_array ((@1 (Type Int))) Deduced)))))))
    |}]

let%expect_test _ =
  parse "x[0];";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Index (@1 (Identifier x)) ((@1 (Int_literal 0))))))))))
    |}]
  
let%expect_test _ =
  parse "z[1] = 2;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (Index (@1 (Identifier z)) ((@1 (Int_literal 1)))))
           (@1 (Int_literal 2)))))))))
    |}]

let%expect_test _ =
  parse "int <- (int, bool);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Type
           (Function (Unevaluated (@1 (Type Int)))
            ((Unevaluated (@1 (Type Int))) (Unevaluated (@1 (Type Bool)))) ()))))))))
    |}]

let%expect_test _ =
  parse "int <- (int) pure;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Type
           (Function (Unevaluated (@1 (Type Int)))
            ((Unevaluated (@1 (Type Int)))) ((pure))))))))))
    |}]

let%expect_test _ =
  parse "int <- (int) const;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Type
           (Function (Unevaluated (@1 (Type Int)))
            ((Unevaluated (@1 (Type Int)))) ((const))))))))))
    |}]

(* Declarations *)

let%expect_test _ =
  parse "int x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name x)
          (init_expr ())))))))
    |}]

let%expect_test _ =
  parse "int x = 2+1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name x)
          (init_expr
           ((@1 (Binary_op Plus (@1 (Int_literal 2)) (@1 (Int_literal 1))))))))))))
    |}]

let%expect_test _ =
  parse "mut int x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ((mut))) (typ (Unevaluated (@1 (Type Int)))) (name x)
          (init_expr ())))))))
    |}]

let%expect_test _ =
  parse "let max = 5;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Assignment (@1 (Let (Identifier max))) (@1 (Int_literal 5)))))))))
    |}]

let%expect_test _ =
  parse "int max(int a, int b) { a > b ? a : b; }";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ()) (typ Deduced) (name max)
          (init_expr
           ((@1
             (Lambda (Unevaluated (@1 (Type Int)))
              ((@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
                  (init_expr ())))))
              ()
              (@1
               (Compound
                ((@1
                  (Expression
                   (@1
                    (Conditional
                     (@1
                      (Binary_op Greater (@1 (Identifier a)) (@1 (Identifier b))))
                     (@1 (Identifier a)) (@1 (Identifier b)))))))))))))))))))
    |}]
 
let%expect_test _ =
  parse "let _ = 7;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Assignment (@1 (Let Any)) (@1 (Int_literal 7)))))))))
    |}]

    
let%expect_test _ =
  parse "_=7;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Assignment (@1 (Let Any)) (@1 (Int_literal 7)))))))))
    |}]

let%expect_test _ =
  parse "(let a, let b) = (1, 2);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment
           (@1 (Tuple ((@1 (Let (Identifier a))) (@1 (Let (Identifier b))))))
           (@1 (Tuple ((@1 (Int_literal 1)) (@1 (Int_literal 2))))))))))))
    |}]

let%expect_test _ =
  parse "(int, int) x = (1, 2);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ())
          (typ (Unevaluated (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int)))))))
          (name x)
          (init_expr ((@1 (Tuple ((@1 (Int_literal 1)) (@1 (Int_literal 2)))))))))))))
    |}]

let%expect_test _ =
  parse "int (int x, int y) f;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ())
          (typ
           (Unevaluated
            (@1 (Call (@1 (Type Int)) ((@1 (Type Int)) (@1 (Type Int))) ()))))
          (name f) (init_expr ())))))))
    |}]

let%expect_test _ =
  parse "let a = 1 in a + 1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (In (@1 (Assignment (@1 (Let (Identifier a))) (@1 (Int_literal 1))))
           (@1 (Binary_op Plus (@1 (Identifier a)) (@1 (Int_literal 1)))))))))))
    |}]

(* Lambdas & calls *)

let%expect_test _ =
  parse "int&() {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Lambda (Unevaluated (@1 (Type Int))) () () (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int&() pure {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int))) () ((pure)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int&() const {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int))) () ((const)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "&() {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Lambda Deduced () () (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int&(int a) const -> let b=a+1 in b;";

  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int)))
           ((@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
               (init_expr ())))))
           ((const))
           (@1
            (Return
             (@1
              (In
               (@1
                (Assignment (@1 (Let (Identifier b)))
                 (@1 (Binary_op Plus (@1 (Identifier a)) (@1 (Int_literal 1))))))
               (@1 (Identifier b)))))))))))))
    |}]

let%expect_test _ =
  parse "int&(int a, int b) {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int)))
           ((@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
               (init_expr ())))))
           () (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int&(int a, int b) pure {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int)))
           ((@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
               (init_expr ())))))
           ((pure)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int&(int a, int b) const {};";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int)))
           ((@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
               (init_expr ()))))
            (@1
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
               (init_expr ())))))
           ((const)) (@1 (Compound ())))))))))
    |}]

let%expect_test _ =
  parse "int foo (int a, int b) {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ()) (typ Deduced) (name foo)
          (init_expr
           ((@1
             (Lambda (Unevaluated (@1 (Type Int)))
              ((@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
                  (init_expr ())))))
              () (@1 (Compound ()))))))))))))
    |}]

let%expect_test _ =
  parse "int foo (int a, int b) pure {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Declaration
         ((modifiers ()) (typ Deduced) (name foo)
          (init_expr
           ((@1
             (Lambda (Unevaluated (@1 (Type Int)))
              ((@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name a)
                  (init_expr ()))))
               (@1
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name b)
                  (init_expr ())))))
              ((pure)) (@1 (Compound ()))))))))))))
    |}]


let%expect_test _ =
  parse "foo();";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Call (@1 (Identifier foo)) () ())))))))
    |}]

let%expect_test _ =
  parse "foo(7);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression (@1 (Call (@1 (Identifier foo)) ((@1 (Int_literal 7))) ())))))))
    |}]

(* We don't support this syntax because we want to avoid this ambiguity:
     return
     2
  After EOL recovery, it be could interpreted as:
    return;
    2;
  or:
    return 2;
  *)
let%expect_test _ =
  parse "return;";
  [% expect{|
    Error line 1, character 7: unexpected ';' symbol
    (@1 (Order_independent ()))
    |}]

let%expect_test _ =
  parse "return 7;";
  [% expect{| (@1 (Order_independent ((@1 (Return (@1 (Int_literal 7))))))) |}]


(* Control flow Statements *)

let%expect_test _ =
  parse "if condition {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (If (@1 (Identifier condition)) (@1 (Compound ())) (@1 (Compound ())))))))
    |}]

let%expect_test _ =
  parse "if condition {} else {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (If (@1 (Identifier condition)) (@1 (Compound ())) (@1 (Compound ())))))))
    |}]

let%expect_test _ =
  parse "while condition {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (If (@1 (Identifier condition))
         (@1 (Do_while (@1 (Compound ())) (@1 (Identifier condition))))
         (@0 (Compound ())))))))
    |}]
   
let%expect_test _ =
  parse "do {} while condition;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Do_while (@1 (Compound ())) (@1 (Identifier condition)))))))
    |}]

let%expect_test _ =
  parse "for int i=0; i<10; i=i+1 {}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Compound
         ((@1
           (Declaration
            ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name i)
             (init_expr ((@1 (Int_literal 0)))))))
          (@1
           (If (@1 (Binary_op Less (@1 (Identifier i)) (@1 (Int_literal 10))))
            (@1
             (Do_while
              (@1
               (Compound
                ((@1 (Compound ()))
                 (@1
                  (Expression
                   (@1
                    (Assignment (@1 (Identifier i))
                     (@1
                      (Binary_op Plus (@1 (Identifier i)) (@1 (Int_literal 1)))))))))))
              (@1 (Binary_op Less (@1 (Identifier i)) (@1 (Int_literal 10))))))
            (@0 (Compound ()))))))))))
    |}]

let%expect_test _ =
  parse {|
    (let a, 2) ~ v in a |
    (let a, _) ~ v when p in a
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Fall_through
           (@2
            (Match (@2 (Tuple ((@2 (Let (Identifier a))) (@2 (Int_literal 2)))))
             (@2 (Identifier v)) (@2 (Bool_literal true)) (@2 (Identifier a))
             (-1 -1)))
           (@3
            (Match (@3 (Tuple ((@3 (Let (Identifier a))) (@3 (Let Any)))))
             (@3 (Identifier v)) (@3 (Identifier p)) (@3 (Identifier a))
             (-1 -1))))))))))
    |}]


let%expect_test _ =
  parse {|
    (let a, 2) ~ v in
      a
  | (let a, _) ~ v when p in
      a
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Fall_through
           (@2
            (Match (@2 (Tuple ((@2 (Let (Identifier a))) (@2 (Int_literal 2)))))
             (@2 (Identifier v)) (@2 (Bool_literal true)) (@3 (Identifier a))
             (-1 -1)))
           (@4
            (Match (@4 (Tuple ((@4 (Let (Identifier a))) (@4 (Let Any)))))
             (@4 (Identifier v)) (@4 (Identifier p)) (@5 (Identifier a))
             (-1 -1))))))))))
    |}]

let%expect_test _ =
  parse {|
    (let a, 2) ~ v in { a; }
  | (let a, _) ~ v when p in { a; }
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Fall_through
           (@2
            (Match (@2 (Tuple ((@2 (Let (Identifier a))) (@2 (Int_literal 2)))))
             (@2 (Identifier v)) (@2 (Bool_literal true))
             (@2
              (Statement (@2 (Compound ((@2 (Expression (@2 (Identifier a)))))))))
             (-1 -1)))
           (@3
            (Match (@3 (Tuple ((@3 (Let (Identifier a))) (@3 (Let Any)))))
             (@3 (Identifier v)) (@3 (Identifier p))
             (@3
              (Statement (@3 (Compound ((@3 (Expression (@3 (Identifier a)))))))))
             (-1 -1))))))))))
    |}]

(* End of line skipping *)

let%expect_test _ =
  parse "1\n-1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Int_literal 1))))
       (@2 (Expression (@2 (Unary_op Negate (@2 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "1-\n1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Minus (@1 (Int_literal 1)) (@2 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse {|
    if c {
    }
    1
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2 (If (@2 (Identifier c)) (@2 (Compound ())) (@2 (Compound ()))))
       (@4 (Expression (@4 (Int_literal 1)))))))
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
     (Order_independent
      ((@2 (If (@2 (Identifier c)) (@3 (Compound ())) (@2 (Compound ()))))
       (@5 (Expression (@5 (Int_literal 1)))))))
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
     (Order_independent
      ((@2 (If (@2 (Identifier c)) (@3 (Compound ())) (@6 (Compound ()))))
       (@8 (Expression (@8 (Int_literal 1)))))))
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
     (Order_independent
      ((@2 (If (@2 (Identifier c)) (@2 (Compound ())) (@4 (Compound ()))))
       (@6 (Expression (@6 (Int_literal 1)))))))
    |}]

let%expect_test _ =
  parse {|
    {
      1
      2
      3
    }
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Compound
         ((@3 (Expression (@3 (Int_literal 1))))
          (@4 (Expression (@4 (Int_literal 2))))
          (@5 (Expression (@5 (Int_literal 3))))))))))
    |}]

let%expect_test _ =
  parse {|
    {
      1
      
      let x = 2
    }
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Compound
         ((@3 (Expression (@3 (Int_literal 1))))
          (@5
           (Expression
            (@5 (Assignment (@5 (Let (Identifier x))) (@5 (Int_literal 2))))))))))))
    |}]

let%expect_test _ =
  parse {|
  void f(int x,
         int y) {
  }
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Declaration
         ((modifiers ()) (typ Deduced) (name f)
          (init_expr
           ((@2
             (Lambda (Unevaluated (@2 (Type (Tuple ()))))
              ((@2
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@2 (Type Int)))) (name x)
                  (init_expr ()))))
               (@3
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@3 (Type Int)))) (name y)
                  (init_expr ())))))
              () (@3 (Compound ()))))))))))))
    |}]

let%expect_test _ =
  parse {|
  void f(
    int x,
    int y
    ) {
  }
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Declaration
         ((modifiers ()) (typ Deduced) (name f)
          (init_expr
           ((@2
             (Lambda (Unevaluated (@2 (Type (Tuple ()))))
              ((@3
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@3 (Type Int)))) (name x)
                  (init_expr ()))))
               (@4
                (Declaration
                 ((modifiers ()) (typ (Unevaluated (@4 (Type Int)))) (name y)
                  (init_expr ())))))
              () (@5 (Compound ()))))))))))))
    |}]

let%expect_test _ =
  parse {|
    (
      1,
      2
      , 3
    );
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Tuple
           ((@3 (Int_literal 1)) (@4 (Int_literal 2)) (@5 (Int_literal 3))))))))))
    |}]

let%expect_test _ =
  parse {|
    [
      1,
      2
      , 3
    ];
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Dynamic_array
           ((@3 (Int_literal 1)) (@4 (Int_literal 2)) (@5 (Int_literal 3)))
           Deduced)))))))
    |}]

let%expect_test _ =
  parse {|
    int&(
      int a
    ) {};
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Lambda (Unevaluated (@2 (Type Int)))
           ((@3
             (Declaration
              ((modifiers ()) (typ (Unevaluated (@3 (Type Int)))) (name a)
               (init_expr ())))))
           () (@4 (Compound ())))))))))
    |}]

  let%expect_test _ =
  parse {|
  let x = f(x,
            y);
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Assignment (@2 (Let (Identifier x)))
           (@2
            (Call (@2 (Identifier f)) ((@2 (Identifier x)) (@3 (Identifier y)))
             ())))))))))
    |}]

let%expect_test _ =
  parse {|
  let x = f(x
          , y);
  |};
  [% expect{|
    (@1
     (Order_independent
      ((@2
        (Expression
         (@2
          (Assignment (@2 (Let (Identifier x)))
           (@2
            (Call (@2 (Identifier f)) ((@2 (Identifier x)) (@3 (Identifier y)))
             ())))))))))
    |}]

(* ERRORS *)

  
let%expect_test _ =
  parse "+; 1+1;";
  [% expect{|
    Error line 1, character 1: unexpected '+' symbol
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "1+; 1+1;";
  [% expect{|
    Error line 1, character 3: unexpected ';' symbol
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "(1; 1+1;";
  [% expect{|
    Error line 1, character 3: unexpected ';' symbol
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "1); 1+1;";
  [% expect{|
    Error line 1, character 2: unexpected ')' symbol
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Binary_op Plus (@1 (Int_literal 1)) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "{a}";
  [% expect{|
    Error line 1, character 3: unexpected '}' symbol
    (@1 (Order_independent ((@1 (Compound ())))))
    |}]

