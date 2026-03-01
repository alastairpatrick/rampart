open Bind
open Const_eval
open Diagnostic
open Error
open LexPass
open Location
open Recovery


let evaluate_declarations text =
  try
    let lexbuf = Lexing.from_string text in
    let tokens = lex_pass lexbuf in
      let statement = parse_recovering (make_diagnostic_sink ()) tokens in
      let env = top_scope () in
      let num_globals, statement = bind_program env statement in
      let global_frame = make_global_frame num_globals in
      let program = evaluate_statement env global_frame Abandon_on_side_effect statement in
      Sexplib.Sexp.output_hum stdout (Ast.sexp_of_statement program)
    with Located_error (location, message) -> Printf.printf "Error: %s %s\n" (show_location location) message

let%expect_test _ =
  evaluate_declarations "1; 2;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1 (Expression (@1 (IntLiteral 1))))
       (@1 (Expression (@1 (IntLiteral 2)))))))
    |}]

let%expect_test _ =
  evaluate_declarations "1 + 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 3))))))) |}]

let%expect_test _ =
  evaluate_declarations "int x; x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (0 0)))
       (@1 (Expression (@1 (IntLiteral 0)))))))
    |}]

let%expect_test _ =
  evaluate_declarations "bool x; x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1 (Expression (@1 (BoolLiteral false)))))))
    |}]

(* Will catch variables of types that do not have default values but also do not have an initializer in a later pass. *)
let%expect_test _ =
  evaluate_declarations "type t; t;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t) (init_expr ()))
         (0 0)))
       (@1 (Expression (@1 (BoundIdentifier t (0 0))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int x = 2; 1 + x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 2)))))
         (0 0)))
       (@1 (Expression (@1 (IntLiteral 3)))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut int x = 2; 1 + x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 2)))))
         (0 0)))
       (@1
        (Expression
         (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (BoundIdentifier x (0 0))))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut int x = 2; int y = x; 1 + y;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 2)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name y)
          (init_expr ((@1 (BoundIdentifier x (0 0))))))
         (1 0)))
       (@1
        (Expression
         (@1 (BinaryOp Plus (@1 (IntLiteral 1)) (@1 (BoundIdentifier y (1 0))))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = int; t;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0)))
       (@1 (Expression (@1 (Type Int)))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = int; t x = 1; x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 1)))))
         (1 0)))
       (@1 (Expression (@1 (IntLiteral 1)))))))
    |}]

(* Test that a lambda is _not_ treated as a constant *)
let%expect_test _ =
  evaluate_declarations "void f() {} f;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () false))))
          (name f)
          (init_expr
           ((@1 (Lambda (@1 (Type Void)) () () (@1 (BoundFrame 0 ())))))))
         (0 0)))
       (@1 (Expression (@1 (BoundIdentifier f (0 0))))))))
    |}]

(* Test that CTCEs are substituted within a lambda, even though it is not called. *)
let%expect_test _ =
  evaluate_declarations "type t = int; t f(t x) { t y = 1+1; }";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) ((@1 (Type Int))) false))))
          (name f)
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
                ((@1
                  (BoundDeclaration
                   ((modifiers ()) (type_expr ((@1 (Type Int)))) (name y)
                    (init_expr ((@1 (IntLiteral 2)))))
                   (1 1)))))))))))
         (1 0))))))
    |}]
