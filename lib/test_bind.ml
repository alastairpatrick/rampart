open Bind
open Diagnostic
open Error
open LexPass
open Location
open Printf
open Recovery

let parse text =
  let lexbuf = Lexing.from_string text in
  let tokens = lex_pass lexbuf in
    try
      let statement = parse_recovering (make_diagnostic_sink ()) tokens in
      let _, bound = bind_program (top_scope ()) statement in
      Sexplib.Sexp.output_hum stdout (Ast.sexp_of_statement bound)
    with
    | Located_error (location, message) -> printf "Error: %s %s" (show_location location) message
    | Error message  -> printf "Error: %s" message
    | Unbound_identifier_error (_, name) -> printf "Error: unbound identifier '%s'" name

let%expect_test _ =
  parse "bool a = true; bool b = a;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name a)
          (init_expr ((@1 (BoolLiteral true)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name b)
          (init_expr ((@1 (BoundIdentifier a (0 0))))))
         (1 0))))))
    |}]

let%expect_test _ =
  parse "let a = [1, 2, 3];";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (0 0)))
           (@1
            (DynamicArrayLiteral
             ((@1 (IntLiteral 1)) (@1 (IntLiteral 2)) (@1 (IntLiteral 3))) ())))))))))
    |}]

let%expect_test _ =
  parse "int[] x;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Index (@1 (Type Int)) ())))) (name x)
          (init_expr ()))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int[] x; let y = x[0];";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Index (@1 (Type Int)) ())))) (name x)
          (init_expr ()))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier y) (1 0)))
           (@1 (Index (@1 (BoundIdentifier x (0 0))) ((@1 (IntLiteral 0))))))))))))
    |}]

let%expect_test _ =
  parse "let z = [1,2][1];";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier z) (0 0)))
           (@1
            (Index
             (@1
              (DynamicArrayLiteral ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))) ()))
             ((@1 (IntLiteral 1))))))))))))
    |}]

let%expect_test _ =
parse "let x;";
  [% expect{|
    (@1
     (OrderIndependent ((@1 (Expression (@1 (BoundLet (Identifier x) (0 0))))))))
    |}]

let%expect_test _ =
  parse "let a = true; let b = a;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (0 0)))
           (@1 (BoolLiteral true))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (1 0)))
           (@1 (BoundIdentifier a (0 0))))))))))
    |}]

let%expect_test _ =
  parse "let b = a; let a = true;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (0 0)))
           (@1 (BoundIdentifier a (1 0)))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1 (BoolLiteral true)))))))))
    |}]

let%expect_test _ =
  parse "(let a, let b);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Tuple
           ((@1 (BoundLet (Identifier a) (0 0)))
            (@1 (BoundLet (Identifier b) (1 0)))))))))))
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
           (@1
            (Tuple
             ((@1 (BoundLet (Identifier a) (0 0)))
              (@1 (BoundLet (Identifier b) (1 0))))))
           (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
    |}]

let%expect_test _ =
  parse "(int, int) x = (1, 2);";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))) (name x)
          (init_expr ((@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "{ let a = true; let b = a; }";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Compound
         ((@1
           (Expression
            (@1
             (Assignment (@1 (BoundLet (Identifier a) (0 0)))
              (@1 (BoolLiteral true))))))
          (@1
           (Expression
            (@1
             (Assignment (@1 (BoundLet (Identifier b) (1 0)))
              (@1 (BoundIdentifier a (0 0)))))))))))))
    |}]

let%expect_test _ =
  parse "{ let b = a; let a = true; }";
  [% expect{| Error: @1 unbound identifier 'a' |}]

let%expect_test _ =
  parse "{ let b = a; } let a = b;";
  [% expect{| Error: @1 unbound identifier 'b' |}]

let%expect_test _ =
  parse "int main() { let a = true; let b = a; }";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ()) (name main)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ()
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundLet (Identifier a) (0 1)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundLet (Identifier b) (1 1)))
                       (@1 (BoundIdentifier a (0 1))))))))))))
              ())))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int foo(int x) {int y = x;}";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ()) (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
                  (init_expr ()))
                 (0 1))))
              ()
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Int)))) (name y)
                      (init_expr ((@1 (BoundIdentifier x (0 1))))))
                     (1 1))))))))
              ())))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int foo(int x) {} int y = x;";
  [% expect{| Error: @1 unbound identifier 'x' |}]

let%expect_test _ =
  parse "let _ = 1;";
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (Assignment (@1 (BoundLet Any (0 0))) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  parse {|
  int fib(int n) {
    if (n == 0) { return 0; }
    if (n == 1) { return 1; }
    return fib(n-2) + fib(n-1);
  }
  |};
  [% expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ()) (name fib)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
                  (init_expr ()))
                 (0 1))))
              ()
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (If
                     (@1
                      (BinaryOp Equals (@1 (BoundIdentifier n (0 1)))
                       (@1 (IntLiteral 0))))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 0)))))))
                     (@1 (Compound ()))))
                   (@1
                    (If
                     (@1
                      (BinaryOp Equals (@1 (BoundIdentifier n (0 1)))
                       (@1 (IntLiteral 1))))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 1)))))))
                     (@1 (Compound ()))))
                   (@1
                    (Return
                     (@1
                      (BinaryOp Plus
                       (@1
                        (Call (@1 (BoundIdentifier fib (0 0)))
                         ((@1
                           (BinaryOp Minus (@1 (BoundIdentifier n (0 1)))
                            (@1 (IntLiteral 2)))))
                         ()))
                       (@1
                        (Call (@1 (BoundIdentifier fib (0 0)))
                         ((@1
                           (BinaryOp Minus (@1 (BoundIdentifier n (0 1)))
                            (@1 (IntLiteral 1)))))
                         ())))))))))))
              ())))))
         (0 0))))))
    |}]
