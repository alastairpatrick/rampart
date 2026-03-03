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

(* This pair of declarations forms a mutual reference (a -> b -> a). The
   const-eval pass only reports cycles when they prevent evaluating a
   declaration's type. Here both declarations' types can still be resolved,
   so the pass returns the normalized program rather than emitting an error.
   General cycle detection is deferred to the static type checker. *)
let%expect_test _ =
  evaluate_declarations "int a = b; int b = a;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
          (init_expr ((@1 (BoundIdentifier b (1 0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
          (init_expr ((@1 (BoundIdentifier a (0 0))))))
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
          (type_expr ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) ()))))
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
          (type_expr ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) ()))))
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
          (type_expr
           ((@1 (Call (@1 (Type Bool)) ((@1 (Type Bool))) ((pure) (const))))))
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

(* Const function can evaluate to declaration type *)
let%expect_test _ =
  evaluate_declarations "type f() const { return int; } f() x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Type)) () ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Annotated External
              (@1
               (Lambda (@1 (Type Type)) () ((pure) (const))
                (@1 (BoundFrame 0 ((@1 (Return ((@1 (Type Int)))))))))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f(type t) const { return (int, t); } f(bool) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Type)) ((@1 (Type Type))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Annotated External
              (@1
               (Lambda (@1 (Type Type))
                ((@1
                  (BoundDeclaration
                   ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
                    (init_expr ()))
                   (0 1))))
                ((pure) (const))
                (@1
                 (BoundFrame 1
                  ((@1
                    (Return
                     ((@1
                       (Tuple ((@1 (Type Int)) (@1 (BoundIdentifier t (0 1)))))))))))))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Bool))))))) (name x)
          (init_expr
           ((@1 (Tuple ((@1 (IntLiteral 0)) (@1 (BoolLiteral false))))))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut type m = bool; type f() const { return m; } f() x;";
  [%expect{| Error: @1 'm' is not a compile-time constant |}]

let%expect_test _ =
  evaluate_declarations "mut type m = bool; type f(type t) const { return t; } f(m) x;";
  [%expect{| Error: @1 'm' is not a compile-time constant |}]

(* TODO: Finish evaluate_assignment to allow this *)
(*let%expect_test _ =
  evaluate_declarations "type f(type t) const { mut type s = t; return s; } f(int) x;";
  [%expect{|  |}]*)

(* A declaration type not evaluating to an actual type might be benign in the const_eval pass; a later pass will catch the error. *)
let%expect_test _ =
  evaluate_declarations "int f() const { return 0; } f() x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const)))))) (name f)
          (init_expr
           ((@1
             (Annotated External
              (@1
               (Lambda (@1 (Type Int)) () ((pure) (const))
                (@1 (BoundFrame 0 ((@1 (Return ((@1 (IntLiteral 0)))))))))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (IntLiteral 0)))) (name x)
          (init_expr ()))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() { return int; } f() x;";
  [%expect{| Error: @1 'f' is not a compile-time constant |}]

(* foo cannot recurse from within a declaration type. *)
let%expect_test _ =
  evaluate_declarations "type t = bool; t foo(t x) const { foo(t) y; }";
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
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const))))))
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

(* Impure nested function can capture mutable variables of const function. *)
(*let%expect_test _ =
  evaluate_declarations "type foo() const { mut type t = int; void bar() { t = bool; } bar(); return t; } foo() x;";
  [%expect{|

    |}]*)

(*
  Regression test (commented out): const function returning a const lambda
  that captures a callee-local variable. This is a subtle escape: even if a
  value passes `is_const_expression` (annotated const lambda), it may close
  over the callee's local frame. The GC prevents dangling pointers, but this
  leaks mutable local state into a supposedly-constant value and should be
  rejected by the const-eval pass.

  The test below uses hypothetical/unfinished syntax and is intentionally
  commented out until the necessary checks and syntax are implemented.

let%expect_test _ =
  evaluate_declarations "int make() const { int x = 1; () const { x; } } int g = make();";
  [%expect{| Error: @1 const lambda escapes callee-local frame |}]
*)

