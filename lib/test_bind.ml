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
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Type Bool)))) (name a)
          (init_expr ((@1 (Bool_literal true)))))
         (0 0)))
       (@1
        (Bound_declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Type Bool)))) (name b)
          (init_expr ((@1 (Bound_identifier a (0 0))))))
         (1 0))))))
    |}]

let%expect_test _ =
  parse "let a = [1, 2, 3];";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier a) (0 0)))
           (@1
            (Dynamic_array
             ((@1 (Int_literal 1)) (@1 (Int_literal 2)) (@1 (Int_literal 3)))
             Deduced)))))))))
    |}]

let%expect_test _ =
  parse "int[] x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Index (@1 (Type Int)) ()))))
          (name x) (init_expr ()))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int[] x; let y = x[0];";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ()) (typ (Unevaluated (@1 (Index (@1 (Type Int)) ()))))
          (name x) (init_expr ()))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier y) (1 0)))
           (@1 (Index (@1 (Bound_identifier x (0 0))) ((@1 (Int_literal 0))))))))))))
    |}]

let%expect_test _ =
  parse "let z = [1,2][1];";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier z) (0 0)))
           (@1
            (Index
             (@1
              (Dynamic_array ((@1 (Int_literal 1)) (@1 (Int_literal 2))) Deduced))
             ((@1 (Int_literal 1))))))))))))
    |}]

let%expect_test _ =
parse "let x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1 (Expression (@1 (Bound_let (Identifier x) (0 0))))))))
    |}]

let%expect_test _ =
  parse "let a = true; let b = a;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier a) (0 0)))
           (@1 (Bool_literal true))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier b) (1 0)))
           (@1 (Bound_identifier a (0 0))))))))))
    |}]

let%expect_test _ =
  parse "let b = a; let a = true;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier b) (0 0)))
           (@1 (Bound_identifier a (1 0)))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (Bound_let (Identifier a) (1 0)))
           (@1 (Bool_literal true)))))))))
    |}]

let%expect_test _ =
  parse "(let a, let b);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Tuple
           ((@1 (Bound_let (Identifier a) (0 0)))
            (@1 (Bound_let (Identifier b) (1 0)))))))))))
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
           (@1
            (Tuple
             ((@1 (Bound_let (Identifier a) (0 0)))
              (@1 (Bound_let (Identifier b) (1 0))))))
           (@1 (Tuple ((@1 (Int_literal 1)) (@1 (Int_literal 2))))))))))))
    |}]

let%expect_test _ =
  parse "(int, int) x = (1, 2);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ())
          (typ (Unevaluated (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int)))))))
          (name x)
          (init_expr ((@1 (Tuple ((@1 (Int_literal 1)) (@1 (Int_literal 2))))))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "{ let a = true; let b = a; }";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Compound
         ((@1
           (Expression
            (@1
             (Assignment (@1 (Bound_let (Identifier a) (0 0)))
              (@1 (Bool_literal true))))))
          (@1
           (Expression
            (@1
             (Assignment (@1 (Bound_let (Identifier b) (1 0)))
              (@1 (Bound_identifier a (0 0)))))))))))))
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
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ()) (typ Deduced) (name main)
          (init_expr
           ((@1
             (Lambda (Unevaluated (@1 (Type Int))) () ()
              (@1
               (Bound_frame 3
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (Bound_let (Identifier a) (1 1)))
                       (@1 (Bool_literal true))))))
                   (@1
                    (Expression
                     (@1
                      (Assignment (@1 (Bound_let (Identifier b) (2 1)))
                       (@1 (Bound_identifier a (1 1)))))))))))))))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int foo(int x) {int y = x;}";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Bound_declaration
         ((modifiers ()) (typ Deduced) (name foo)
          (init_expr
           ((@1
             (Lambda (Unevaluated (@1 (Type Int)))
              ((@1
                (Bound_declaration
                 ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name x)
                  (init_expr ()))
                 (0 1))))
              ()
              (@1
               (Bound_frame 3
                (@1
                 (Compound
                  ((@1
                    (Bound_declaration
                     ((modifiers ()) (typ (Unevaluated (@1 (Type Int))))
                      (name y) (init_expr ((@1 (Bound_identifier x (0 1))))))
                     (2 1)))))))))))))
         (0 0))))))
    |}]

let%expect_test _ =
  parse "int foo(int x) {} int y = x;";
  [% expect{| Error: @1 unbound identifier 'x' |}]

let%expect_test _ =
  parse "let _ = 1;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1 (Assignment (@1 (Bound_let Any (-1 -1))) (@1 (Int_literal 1)))))))))
    |}]

let%expect_test _ =
  parse "let a in a;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (In (@1 (Bound_let (Identifier a) (0 0)))
           (@1 (Bound_identifier a (0 0))))))))))
    |}]

let%expect_test _ =
  parse "let a ~ 1 in a;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Match (@1 (Bound_let (Identifier a) (0 0))) (@1 (Int_literal 1))
           (@1 (Bool_literal true)) (@1 (Bound_identifier a (0 0))) (1 0))))))))
    |}]

let%expect_test _ =
  parse "let a ~ true when a in a;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Match (@1 (Bound_let (Identifier a) (0 0))) (@1 (Bool_literal true))
           (@1 (Bound_identifier a (0 0))) (@1 (Bound_identifier a (0 0)))
           (1 0))))))))
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
     (Order_independent
      ((@2
        (Bound_declaration
         ((modifiers ()) (typ Deduced) (name fib)
          (init_expr
           ((@2
             (Lambda (Unevaluated (@2 (Type Int)))
              ((@2
                (Bound_declaration
                 ((modifiers ()) (typ (Unevaluated (@2 (Type Int)))) (name n)
                  (init_expr ()))
                 (0 1))))
              ()
              (@2
               (Bound_frame 2
                (@2
                 (Compound
                  ((@3
                    (If
                     (@3
                      (Binary_op Equals (@3 (Bound_identifier n (0 1)))
                       (@3 (Int_literal 0))))
                     (@3 (Compound ((@3 (Return (@3 (Int_literal 0)))))))
                     (@3 (Compound ()))))
                   (@4
                    (If
                     (@4
                      (Binary_op Equals (@4 (Bound_identifier n (0 1)))
                       (@4 (Int_literal 1))))
                     (@4 (Compound ((@4 (Return (@4 (Int_literal 1)))))))
                     (@4 (Compound ()))))
                   (@5
                    (Return
                     (@5
                      (Binary_op Plus
                       (@5
                        (Call (@5 (Bound_identifier fib (0 0)))
                         ((@5
                           (Binary_op Minus (@5 (Bound_identifier n (0 1)))
                            (@5 (Int_literal 2)))))
                         ()))
                       (@5
                        (Call (@5 (Bound_identifier fib (0 0)))
                         ((@5
                           (Binary_op Minus (@5 (Bound_identifier n (0 1)))
                            (@5 (Int_literal 1)))))
                         ()))))))))))))))))
         (0 0))))))
    |}]
