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
      let program = evaluate_statement env global_frame Search_for_declaration_types statement in
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
  evaluate_declarations "type t = int; t x;";
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
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = bool; t x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = type; t x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Type)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name x) (init_expr ()))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = (int, int); t x = (1, 2);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))) (name x)
          (init_expr ((@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))
         (1 0))))))
    |}]

(* Declarations types within foo are evaluated, even if foo is not called *)
let%expect_test _ =
  evaluate_declarations "t foo(t x) { t y; } type t = bool;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) false))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Bool))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
                  (init_expr ()))
                 (0 1))))
              ()
              (@1
               (BoundFrame 2
                ((@1
                  (BoundDeclaration
                   ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                    (init_expr ((@1 (BoolLiteral false)))))
                   (1 1)))))))))))
         (0 0))))))
    |}]

(* expressions within foo can bind to foo, eg to recurse, so long as not from within a declaration type. *)
let%expect_test _ =
  evaluate_declarations "t foo(t x) { t y; foo; } type t = bool;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) false))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Bool))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
                  (init_expr ()))
                 (0 1))))
              ()
              (@1
               (BoundFrame 2
                ((@1
                  (BoundDeclaration
                   ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                    (init_expr ((@1 (BoolLiteral false)))))
                   (1 1)))
                 (@1 (Expression (@1 (BoundIdentifier foo (0 0)))))))))))))
         (0 0))))))
    |}]
let%expect_test _ =
  evaluate_declarations "t foo(t x) const { t y; foo; } type t = bool;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) false))))
          (name foo)
          (init_expr
           ((@1
             (Annotated External
              (@1
               (Lambda (@1 (Type Bool))
                ((@1
                  (BoundDeclaration
                   ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
                    (init_expr ()))
                   (0 1))))
                ((pure) (const))
                (@1
                 (BoundFrame 2
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                      (init_expr ((@1 (BoolLiteral false)))))
                     (1 1)))
                   (@1 (Expression (@1 (BoundIdentifier foo (0 0)))))))))))))))
         (0 0))))))
    |}]

(* foo cannot recurse from within a declaration type. *)
let%expect_test _ =
  evaluate_declarations "type t = bool; t foo(t x) const { foo y; }";
  (* evaluate_declarations "type t = bool; t foo(t x) const { foo(t) y; }"; TODO: replace above with this when calls are supported *)
  [%expect{| Error: @1 found cyclic dependency: foo -> foo |}]

(* Const functions must not capture mutable variables. Note that this pass only catches this error if the function is called. *)
(* TODO: calls not yet implemented *)
(*let%expect_test _ =
  evaluate_declarations "int foo() const { x; } foo(); mut int x;";
  [%expect{| Error: @1 'x' is not a compile-time constant |}]*)

  
(* Const functions must not capture non-const variables. Note that this pass only catches this error if the function is called. *)
(* TODO: calls not yet implemented *)
(*let%expect_test _ =
  evaluate_declarations "int x = y; int foo() const { x; } foo(); mut int y;";
  [%expect{| Error: @1 'x' is not a compile-time constant |}]*)

(* Const function can capture const variables. *)
let%expect_test _ =
  evaluate_declarations "int foo() const { x; } int x = 7;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Int)) () false))))
          (name foo)
          (init_expr
           ((@1
             (Annotated External
              (@1
               (Lambda (@1 (Type Int)) () ((pure) (const))
                (@1
                 (BoundFrame 0
                  ((@1 (Expression (@1 (BoundIdentifier x (1 0)))))))))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 7)))))
         (1 0))))))
    |}]

