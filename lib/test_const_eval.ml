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
  evaluate_declarations "1 - 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral -1))))))) |}]

let%expect_test _ =
  evaluate_declarations "2 * 3;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 6))))))) |}]

let%expect_test _ =
  evaluate_declarations "5 / 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 2))))))) |}]

let%expect_test _ =
  evaluate_declarations "5 % 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 1))))))) |}]

let%expect_test _ =
  evaluate_declarations "1 < 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  evaluate_declarations "1 <= 1;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  evaluate_declarations "2 > 3;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  evaluate_declarations "3 >= 3;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

(* division by zero stays as BinaryOp during search *)
let%expect_test _ =
  evaluate_declarations "1 / 0;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression (@1 (BinaryOp Div (@1 (IntLiteral 1)) (@1 (IntLiteral 0)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "1 % 0;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Modulo (@1 (IntLiteral 1)) (@1 (IntLiteral 0)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(1 / 0);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return 1 / 0; } f() x;";
  [%expect{| Error: @1 invalid operation: division by zero |}]

let%expect_test _ =
  evaluate_declarations "1 == true;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(1 % 0);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return 1 % 0; } f() x;";
  [%expect{| Error: @1 invalid operation: division by zero |}]

let%expect_test _ =
  evaluate_declarations "true ? 1 : 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 1))))))) |}]

let%expect_test _ =
  evaluate_declarations "false ? 1 : 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 2))))))) |}]

(* Static type checking will catch this error later. *)
let%expect_test _ =
  evaluate_declarations "1 ? 1 : 2;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Conditional (@1 (IntLiteral 1)) (@1 (IntLiteral 1))
           (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut bool c; c ? 1 : 2;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name c)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Conditional (@1 (BoundIdentifier c (0 0))) (@1 (IntLiteral 1))
           (@1 (IntLiteral 2)))))))))
    |}]


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
  evaluate_declarations "type t = type; t x = int;";
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
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name x)
          (init_expr ((@1 (Type Int)))))
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

let%expect_test _ =
  evaluate_declarations "type t = typeof((1+1, 2));";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "typeof(1+1) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut bool c; typeof(c ? 1 : 2) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name c)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut bool called = false; int f() { called = true; return 0; } type t = typeof(f());";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name called)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Int)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier called (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1 (Return (@1 (IntLiteral 0)))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (2 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() const { return 0; } type t = typeof(f());";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const)))))) (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (IntLiteral 0)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() { return 0; } mut int x = f(); type t = typeof(x);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Int)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ()
              (@1
               (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (IntLiteral 0)))))))))
              ())))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (Call (@1 (BoundIdentifier f (0 0))) () ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (2 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut int x; typeof(x = 1) y;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name y)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "typeof(\\void(bool x) {}) y = \\void(bool x) {};";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Void)) ((@1 (Type Bool))) ()))))
          (name y)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
                  (init_expr ()))
                 (0 1))))
              () (@1 (BoundFrame 1 (@1 (Compound ())))) ())))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(\\void(bool x) {});";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Call (@1 (Type Void)) ((@1 (Type Bool))) ())))))
         (0 0))))))
    |}]

(* Evaluates f() and stores the result value arity in n. *)
let%expect_test _ =
  evaluate_declarations "mut bool changed; (int, int) f() { changed = true; return (1, 2); } int n = arity(f());";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name changed)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier changed (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Return
                     (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
          (init_expr
           ((@1 (Arity (@1 (Call (@1 (BoundIdentifier f (1 0))) () ())))))))
         (2 0))))))
    |}]

(* Evaluates f() and stores the result value arity in n. *)
let%expect_test _ =
  evaluate_declarations "mut bool changed; (int, int) f() { changed = true; return (1, 2); } int n = arity(f());";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name changed)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier changed (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Return
                     (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
          (init_expr
           ((@1 (Arity (@1 (Call (@1 (BoundIdentifier f (1 0))) () ())))))))
         (2 0))))))
    |}]

(* Evaluates f() and stores the result value arity in n. *)
let%expect_test _ =
  evaluate_declarations "mut bool changed; (int, int) f() { changed = true; return (1, 2); } int n = arity(typeof(f()));";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name changed)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier changed (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Return
                     (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
          (init_expr
           ((@1 (Arity (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))))))
         (2 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int a = arity(typeof(b)); int b = arity(typeof(a));";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
          (init_expr ((@1 (Arity (@1 (Type Int)))))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
          (init_expr ((@1 (Arity (@1 (Type Int)))))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut bool changed; (int, int) f() { changed = true; return (1, 2); } typeof(arity(f())) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name changed)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier changed (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Return
                     (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (2 0))))))
    |}]


let%expect_test _ =
  evaluate_declarations "mut bool changed; (int, int) f() { changed = true; return (1, 2); } type t = typeof(arity(f()));";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Bool)))) (name changed)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier changed (0 0)))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Return
                     (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2))))))))))))
              ())))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (2 0))))))
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
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                      (init_expr ((@1 (BoolLiteral false)))))
                     (1 1))))))))
              ())))))
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
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                      (init_expr ((@1 (BoolLiteral false)))))
                     (1 1)))
                   (@1 (Expression (@1 (BoundIdentifier foo (0 0))))))))))
              ())))))
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
             (Lambda (@1 (Type Bool))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name y)
                      (init_expr ((@1 (BoolLiteral false)))))
                     (1 1)))
                   (@1 (Expression (@1 (BoundIdentifier foo (0 0))))))))))
              (Closure))))))
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (Type Int)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let f = (\\type() const -> int); f() x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier f) (0 0)))
           (@1
            (Lambda (@1 (Type Type)) () ((pure) (const))
             (@1 (BoundFrame 0 (@1 (Return (@1 (Type Int)))))) (Closure)))))))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "(let f, let i) = (\\type() const -> int, 2); f() x; type t = typeof(i);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment
           (@1
            (Tuple
             ((@1 (BoundLet (Identifier f) (0 0)))
              (@1 (BoundLet (Identifier i) (1 0))))))
           (@1
            (Tuple
             ((@1
               (Lambda (@1 (Type Type)) () ((pure) (const))
                (@1 (BoundFrame 0 (@1 (Return (@1 (Type Int)))))) (Closure)))
              (@1 (IntLiteral 2)))))))))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (2 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (3 0))))))
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
             (Lambda (@1 (Type Type))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (Return
                     (@1
                      (Tuple ((@1 (Type Int)) (@1 (BoundIdentifier t (0 1)))))))))))))
              (Closure))))))
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

let%expect_test _ =
  evaluate_declarations "type f(type t) const { mut type s = t; return s; } f(int) x;";
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
             (Lambda (@1 (Type Type))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut))) (type_expr ((@1 (Type Type))))
                      (name s) (init_expr ((@1 (BoundIdentifier t (0 1))))))
                     (1 1)))
                   (@1 (Return (@1 (BoundIdentifier s (1 1))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return true ? int : bool; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (Type Int)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return false ? int : bool; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (Type Bool)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f(int c) const { return c ? int : bool; } f(7) x;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "type int_vector(int n) const { return n == 0 ? () : (int, int_vector(n-1)); } int_vector(3) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Type)) ((@1 (Type Int))) ((pure) (const))))))
          (name int_vector)
          (init_expr
           ((@1
             (Lambda (@1 (Type Type))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (Return
                     (@1
                      (Conditional
                       (@1
                        (BinaryOp Equals (@1 (BoundIdentifier n (0 1)))
                         (@1 (IntLiteral 0))))
                       (@1 (Tuple ()))
                       (@1
                        (Tuple
                         ((@1 (Type Int))
                          (@1
                           (Call (@1 (BoundIdentifier int_vector (0 0)))
                            ((@1
                              (BinaryOp Minus (@1 (BoundIdentifier n (0 1)))
                               (@1 (IntLiteral 1)))))
                            ()))))))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Tuple
              ((@1 (Type Int))
               (@1
                (Tuple
                 ((@1 (Type Int)) (@1 (Tuple ((@1 (Type Int)) (@1 (Tuple ())))))))))))))
          (name x)
          (init_expr
           ((@1
             (Tuple
              ((@1 (IntLiteral 0))
               (@1
                (Tuple
                 ((@1 (IntLiteral 0))
                  (@1 (Tuple ((@1 (IntLiteral 0)) (@1 (Tuple ()))))))))))))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() const { return 0; } f() x;";
  [%expect{| Error: @1 expected a type |}]

let%expect_test _ =
  evaluate_declarations "type f() { return int; } f() x;";
  [%expect{| Error: @1 'f' is not a compile-time constant |}]

(* foo cannot recurse from within a declaration type. *)
let%expect_test _ =
  evaluate_declarations "type t = bool; t foo(t x) const { foo(t) y; }";
  [%expect{| Error: @1 found cyclic dependency: foo -> foo |}]

(* Const functions must not capture mutable variables. Note that this pass only catches this error if the function is called. *)
let%expect_test _ =
  evaluate_declarations "type foo() const { x; return int; } foo() z; mut int x;";
  [%expect{| Error: @1 'x' is not a compile-time constant |}]
  
(* Const functions must not capture non-const variables. *)
let%expect_test _ =
  evaluate_declarations "int x = y; type foo() const { x; return int; } foo() z; mut int y;";
  [%expect{| Error: @1 'x' is not a compile-time constant |}]

let%expect_test _ =
  evaluate_declarations "type f() const { mut int x; type g() const { x; return int; } return g(); } f() y;";
  [%expect{| Error: @1 cannot access mutable captured variable 'x' from pure context |}]

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
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1
                 (Compound ((@1 (Expression (@1 (BoundIdentifier x (1 0))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 7)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int foo() const { x; } let x = 7;";
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
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1
                 (Compound ((@1 (Expression (@1 (BoundIdentifier x (1 0))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 7)))))))))
    |}]

(* Const function can mutate local frame. *)
let%expect_test _ =
  evaluate_declarations "type foo() const { mut type t = int; t = bool; return t; } foo() x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Type)) () ((pure) (const))))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut))) (type_expr ((@1 (Type Type))))
                      (name t) (init_expr ((@1 (Type Int)))))
                     (0 1)))
                   (@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier t (0 1)))
                       (@1 (Type Bool))))))
                   (@1 (Return (@1 (BoundIdentifier t (0 1))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

(* Const function cannot mutate immutable variables. *)
let%expect_test _ =
  evaluate_declarations "type foo() const { int x; x = 1; return int; } foo() y;";
  [%expect{| Error: @1 cannot assign to immutable variable 'x' |}]

(* Const function cannot mutate immutable captured variables. *)
let%expect_test _ =
  evaluate_declarations "int x; type foo() const { x = 1; return int; } foo() y;";
  [%expect{| Error: @1 cannot assign to immutable variable 'x' |}]

let%expect_test _ =
  evaluate_declarations "type foo() const { x = 1; return int; } foo() y; int x;";
  [%expect{| Error: @1 cannot assign to immutable variable 'x' |}]

(* Const function cannot mutate mutable captured variables. *)
let%expect_test _ =
  evaluate_declarations "mut int x; type foo() const { x = 1; return int; } foo() y;";
  [%expect{| Error: @1 cannot access mutable captured variable 'x' from pure context |}]

(* Lambda nested within const lambda must itself be const *)
let%expect_test _ =
  evaluate_declarations "type foo() const { type t = int; type bar() { return t; } return bar; } void f(foo()() x) {}";
  [%expect{| Error: @1 expected a const lambda |}]

(* Const function can call another const function *)
let%expect_test _ =
  evaluate_declarations "type a() const { return int; } type b() const { return a(); } b() x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Type)) () ((pure) (const))))))
          (name a)
          (init_expr
           ((@1
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (Type Int)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Type)) () ((pure) (const))))))
          (name b)
          (init_expr
           ((@1
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1 (Return (@1 (Call (@1 (BoundIdentifier a (0 0))) () ())))))))))
              (Closure))))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (2 0))))))
    |}]

(* Const function cannot call non-const function *)
let%expect_test _ =
  evaluate_declarations "type a() { return int; } type b() const { return a(); } b() x;";
  [%expect{| Error: @1 'a' is not a compile-time constant |}]

(* Nested const function captures caller's frame. The return value of 'foo' has function type and foo's closure escapes, when it returns 'bar', which refers to a nested lambda that captures 't'.*)
let%expect_test _ =
  evaluate_declarations "(type() const) foo() const { type t = int; type bar() const { return t; } return bar; } foo()() y;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Call (@1 (Call (@1 (Type Type)) () ((pure) (const)))) ()
              ((pure) (const))))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Call (@1 (Type Type)) () ((pure) (const)))) ()
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
                      (init_expr ((@1 (Type Int)))))
                     (0 1)))
                   (@1
                    (BoundDeclaration
                     ((modifiers ())
                      (type_expr
                       ((@1 (Call (@1 (Type Type)) () ((pure) (const))))))
                      (name bar)
                      (init_expr
                       ((@1
                         (Lambda (@1 (Type Type)) () ((pure) (const))
                          (@1
                           (BoundFrame 0
                            (@1
                             (Compound
                              ((@1 (Return (@1 (BoundIdentifier t (0 1))))))))))
                          (Closure))))))
                     (1 1)))
                   (@1 (Return (@1 (BoundIdentifier bar (1 1))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name y)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { let t = (int, bool); return t; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundLet (Identifier t) (0 1)))
                       (@1 (Tuple ((@1 (Type Int)) (@1 (Type Bool)))))))))
                   (@1 (Return (@1 (BoundIdentifier t (0 1))))))))))
              (Closure))))))
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
  evaluate_declarations "type f() const { let t = int; t = bool; return t; } f() x;";
  [%expect{| Error: @1 cannot assign to immutable variable 't' |}]

let%expect_test _ =
  evaluate_declarations "type f() const { (let s, let t) = (int, bool); return t; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Tuple
                         ((@1 (BoundLet (Identifier s) (0 1)))
                          (@1 (BoundLet (Identifier t) (1 1))))))
                       (@1 (Tuple ((@1 (Type Int)) (@1 (Type Bool)))))))))
                   (@1 (Return (@1 (BoundIdentifier t (1 1))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { (let s, (let t, let u)) = (int, (bool, int)); return t; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 3
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Tuple
                         ((@1 (BoundLet (Identifier s) (0 1)))
                          (@1
                           (Tuple
                            ((@1 (BoundLet (Identifier t) (1 1)))
                             (@1 (BoundLet (Identifier u) (2 1)))))))))
                       (@1
                        (Tuple
                         ((@1 (Type Int))
                          (@1 (Tuple ((@1 (Type Bool)) (@1 (Type Int))))))))))))
                   (@1 (Return (@1 (BoundIdentifier t (1 1))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { (let s, let t) = int; return t; } f() x;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "type f() const { (let s, let t) = (int, int, int); return t; } f() x;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "type f() const { let s; return s; } f() x;";
  [%expect{| Error: @1 'let' expressions may only appear to the left of an assignment |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return let s = int in s;} f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (Return
                     (@1
                      (In
                       (@1
                        (Assignment (@1 (BoundLet (Identifier s) (0 1)))
                         (@1 (Type Int))))
                       (@1 (BoundIdentifier s (0 1))))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let x = 1 in x+1;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (In
           (@1
            (Assignment (@1 (BoundLet (Identifier x) (0 0))) (@1 (IntLiteral 1))))
           (@1
            (BinaryOp Plus (@1 (BoundIdentifier x (0 0))) (@1 (IntLiteral 1)))))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(let x = 1 in x+1);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof((let x, let y) = (1, 2) in x+y);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut int y; type t = typeof((let x, y) = (1, 2) in x+y);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name y)
          (init_expr ((@1 (IntLiteral 0)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { () = (); return int; } f() x;";
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
             (Lambda (@1 (Type Type)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1
                    (Expression
                     (@1 (Assignment (@1 (Tuple ())) (@1 (Tuple ()))))))
                   (@1 (Return (@1 (Type Int)))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int make() const { int x = 1; return \\int() const { return x; }; } int g = make();";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const))))))
          (name make)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
                      (init_expr ((@1 (IntLiteral 1)))))
                     (0 1)))
                   (@1
                    (Return
                     (@1
                      (Lambda (@1 (Type Int)) () ((pure) (const))
                       (@1
                        (BoundFrame 0
                         (@1
                          (Compound
                           ((@1 (Return (@1 (BoundIdentifier x (0 1))))))))))
                       (Closure))))))))))
              (Closure))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name g)
          (init_expr ((@1 (Call (@1 (BoundIdentifier make (0 0))) () ())))))
         (1 0))))))
    |}]

(* Invalid implicit conversion during const evaluation *)
let%expect_test _ =
  evaluate_declarations "type f() const { int x = false; return int; } f() x;";
  [%expect{| Error: @1 type mismatch |}]

(* Functions with return type other than 'void' must explicitly return.
   This is motivated by there being an implicit conversion from () to type, so the
   snippet below would actually type check without this additional rule. *)
let%expect_test _ =
  evaluate_declarations "type f() const {} f() x;";
  [%expect{| Error: @1 missing return statement |}]
