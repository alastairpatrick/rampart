open Bind
open Const
open Const_eval
open Diagnostic
open Error
open LexPass
open Location
open Recovery


let evaluate_declarations text =
  reset_loop_count();
  dangerously_reset_distinct_closure_identity();
  try
    let lexbuf = Lexing.from_string text in
    let tokens = lex_pass lexbuf in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    let env = top_scope () in
    let num_globals, statement = bind_program env statement in
    let global_frame = make_global_frame num_globals in
    let program = const_evaluate_program env global_frame statement in
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

let%expect_test _ =
  evaluate_declarations "5 & 3;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 1))))))) |}]

let%expect_test _ =
  evaluate_declarations "5 | 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 7))))))) |}]

let%expect_test _ =
  evaluate_declarations "5 ^ 1;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 4))))))) |}]

let%expect_test _ =
  evaluate_declarations "1 << 2;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 4))))))) |}]

let%expect_test _ =
  evaluate_declarations "8 >> 1;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral 4))))))) |}]

let%expect_test _ =
  evaluate_declarations "-8 >> 1;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral -4))))))) |}]

let%expect_test _ =
  evaluate_declarations "true & false;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  evaluate_declarations "true | false;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  evaluate_declarations "true ^ true;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  evaluate_declarations "~0;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (IntLiteral -1))))))) |}]

let%expect_test _ =
  evaluate_declarations "!true;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  evaluate_declarations "!false;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  evaluate_declarations "true && false;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral false))))))) |}]

let%expect_test _ =
  evaluate_declarations "false || true;";
  [%expect{| (@1 (OrderIndependent ((@1 (Expression (@1 (BoolLiteral true))))))) |}]

let%expect_test _ =
  evaluate_declarations "let x = (1<2) || false;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (0 0)))
           (@1 (BoolLiteral true)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(false || true);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(true && false);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof(false || 0);";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "int a = 1; int b = a; int c = b;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
          (init_expr ((@1 (IntLiteral 1)))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
          (init_expr ((@1 (IntLiteral 1)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name c)
          (init_expr ((@1 (IntLiteral 1)))))
         (2 0))))))
    |}]

(* Ultimately, e's initializer is int literal 2 *)
let%expect_test _ =
  evaluate_declarations "void f() {} let a = (f, 1); let b = a; (let c, let d) = b; let e = d+d; let t = typeof(d+d);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1 (Tuple ((@1 (BoundIdentifier f (0 0))) (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (2 0)))
           (@1
            (Tuple
             ((@1 (Index (@1 (BoundIdentifier a (1 0))) ((@1 (IntLiteral 0)))))
              (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment
           (@1
            (Tuple
             ((@1 (BoundLet (Identifier c) (3 0)))
              (@1 (BoundLet (Identifier d) (4 0))))))
           (@1
            (Tuple
             ((@1 (Index (@1 (BoundIdentifier b (2 0))) ((@1 (IntLiteral 0)))))
              (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier e) (5 0))) (@1 (IntLiteral 2))))))
       (@1
        (Expression
         (@1 (Assignment (@1 (BoundLet (Identifier t) (6 0))) (@1 (Type Int)))))))))
    |}]

(* d has int literal 1 initializer*)
let%expect_test _ =
  evaluate_declarations "void f() {} let a = [(f, 0), (f, 1)]; (let b, let c) = a[1]; let d = c;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1
            (DynamicArray
             ((@1 (Tuple ((@1 (BoundIdentifier f (0 0))) (@1 (IntLiteral 0)))))
              (@1 (Tuple ((@1 (BoundIdentifier f (0 0))) (@1 (IntLiteral 1))))))
             ((@1 (Tuple ((@1 (Call (@1 (Type Void)) () ())) (@1 (Type Int))))))))))))
       (@1
        (Expression
         (@1
          (Assignment
           (@1
            (Tuple
             ((@1 (BoundLet (Identifier b) (2 0)))
              (@1 (BoundLet (Identifier c) (3 0))))))
           (@1
            (Tuple
             ((@1
               (Index
                (@1 (Index (@1 (BoundIdentifier a (1 0))) ((@1 (IntLiteral 1)))))
                ((@1 (IntLiteral 0)))))
              (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier d) (4 0))) (@1 (IntLiteral 1)))))))))
    |}]

(* d does _not_ have a lambda initializer; lambdas are environment dependent and cannot be relocated in the AST *)
let%expect_test _ =
  evaluate_declarations "void f() {} let a = [f, f]; let b = a[1];";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1
            (DynamicArray
             ((@1 (BoundIdentifier f (0 0))) (@1 (BoundIdentifier f (0 0))))
             ((@1 (Call (@1 (Type Void)) () ())))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (2 0)))
           (@1 (Index (@1 (BoundIdentifier a (1 0))) ((@1 (IntLiteral 1))))))))))))
    |}]

(* b evaluates to literal true*)
let%expect_test _ =
  evaluate_declarations "void f() {} let a = (f, 1); let b = a == a;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1 (Tuple ((@1 (BoundIdentifier f (0 0))) (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (2 0)))
           (@1 (BoolLiteral true)))))))))
    |}]


(* a evaluates to literal 3 *)
let%expect_test _ =
  evaluate_declarations "int f(int a, int b) const { return a+b; } let a = f(1, 2) const;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Call (@1 (Type Int)) ((@1 (Type Int)) (@1 (Type Int)))
              ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
                  (init_expr ()))
                 (0 1)))
               (@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name b)
                  (init_expr ()))
                 (1 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (Return
                     (@1
                      (BinaryOp Plus (@1 (BoundIdentifier a (0 1)))
                       (@1 (BoundIdentifier b (1 1))))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0))) (@1 (IntLiteral 3)))))))))
    |}]

(* f evaluates to true literal *)
let%expect_test _ =
  evaluate_declarations "void f() {} let a = [f, f]; let b = a[1] == f;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1
            (DynamicArray
             ((@1 (BoundIdentifier f (0 0))) (@1 (BoundIdentifier f (0 0))))
             ((@1 (Call (@1 (Type Void)) () ())))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (2 0)))
           (@1 (BoolLiteral true)))))))))
    |}]


let%expect_test _ =
  evaluate_declarations "void f() {} let a = (f, 1); let b = arity(a);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Void)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ()
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (1 0)))
           (@1 (Tuple ((@1 (BoundIdentifier f (0 0))) (@1 (IntLiteral 1)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (2 0))) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "(true && false ? int : bool) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "(false || true ? int : bool) x;";
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
  evaluate_declarations "(false || 0 ? int : bool) x;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "((true || (1/0 == 1)) ? int : bool) x;";
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
  evaluate_declarations "((false && (1/0 == 1)) ? int : bool) x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "typeof(1 ? 2 : 3) x;";
  [%expect{| Error: @1 type mismatch |}]

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
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1 (BinaryOp Equals (@1 (IntLiteral 1)) (@1 (BoolLiteral true)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut int a; mut bool b; type t = typeof(a == b);";
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

(* This pair of declarations forms a mutual reference (a -> b -> a). *)
let%expect_test _ =
  evaluate_declarations "int a = b; int b = a;";
  [%expect{| Error: @1 found cyclic dependency: b -> a -> b |}]

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
              (0))))))
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
              (0))))))
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
              (0))))))
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
              () (@1 (BoundFrame 1 (@1 (Compound ())))) (0))))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
          (init_expr ((@1 (IntLiteral 2)))))
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
          (init_expr ((@1 (IntLiteral 1)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name a)
          (init_expr ((@1 (IntLiteral 1)))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
         (0 0))))))
    |}]

(* When a function declaration is restarted because of a dependency, the associated closure identity is retained from the first attempt. *)
let%expect_test _ =
  evaluate_declarations "int f() { return x; } bool p = f == g; let x = 0; let g = f;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (2 0))) (@1 (IntLiteral 0))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier g) (3 0)))
           (@1 (BoundIdentifier f (0 0)))))))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Int)) () ()))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ()
              (@1
               (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (IntLiteral 0)))))))))
              (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name p)
          (init_expr ((@1 (BoolLiteral true)))))
         (1 0))))))
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
              (0))))))
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
             (@1 (BoundFrame 0 (@1 (Return (@1 (Type Int)))))) (0)))))))
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
                (@1 (BoundFrame 0 (@1 (Return (@1 (Type Int)))))) (0)))
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
              (0))))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
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
              (0))))))
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
  [%expect {| Error: @1 invalid operation: cannot call non-const lambda in a constant expression |}]

(* foo cannot recurse from within a declaration type. Test disabled because it currently hangs. *)
(*let%expect_test _ =
  evaluate_declarations "type foo() const { foo() y; return int; }";
  [%expect{| Hang preventer aborts unterminated recursion |}]*)

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
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 7)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const))))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1 (Compound ((@1 (Expression (@1 (IntLiteral 7)))))))))
              (0))))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int foo() const { x; } let x = 7;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 7))))))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Int)) () ((pure) (const))))))
          (name foo)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0
                (@1 (Compound ((@1 (Expression (@1 (IntLiteral 7)))))))))
              (0))))))
         (0 0))))))
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
              (0))))))
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
              (0))))))
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
              (1))))))
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
  [%expect{| Error: @1 invalid operation: cannot call non-const lambda in a constant expression |}]

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
                            (@1 (Compound ((@1 (Return (@1 (Type Int)))))))))
                          (1))))))
                     (1 1)))
                   (@1 (Return (@1 (BoundIdentifier bar (1 1))))))))))
              (0))))))
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
                   (@1 (Return (@1 (Tuple ((@1 (Type Int)) (@1 (Type Bool))))))))))))
              (0))))))
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
                   (@1 (Return (@1 (Type Bool)))))))))
              (0))))))
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
                   (@1 (Return (@1 (Type Bool)))))))))
              (0))))))
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
                       (@1 (Type Int)))))))))))
              (0))))))
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
           (@1 (IntLiteral 2)))))))))
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
              (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int() const make() const { int x = 1; return \\int() const { return x; }; } int g = make() const;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Call (@1 (Call (@1 (Type Int)) () ((pure) (const)))) ()
              ((pure) (const))))))
          (name make)
          (init_expr
           ((@1
             (Lambda (@1 (Call (@1 (Type Int)) () ((pure) (const)))) ()
              ((pure) (const))
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
                         (@1 (Compound ((@1 (Return (@1 (IntLiteral 1)))))))))
                       (1))))))))))
              (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name g)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ((pure) (const))
              (@1
               (BoundFrame 0 (@1 (Compound ((@1 (Return (@1 (IntLiteral 1)))))))))
              (4))))))
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

(* Lambda value equality *)
let%expect_test _ =
  evaluate_declarations "void f() const {} (f == f) ? int : bool x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Void)) () ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "void f() const {} void g() const {} (f == g) ? int : bool x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Void)) () ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ())))) (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr ((@1 (Call (@1 (Type Void)) () ((pure) (const))))))
          (name g)
          (init_expr
           ((@1
             (Lambda (@1 (Type Void)) () ((pure) (const))
              (@1 (BoundFrame 0 (@1 (Compound ())))) (1))))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (2 0))))))
    |}]

(* f() == f() evaluates to false here because each call to f() returns a new closure with a unique identity *)
let%expect_test _ =
  evaluate_declarations "(void() const) f() const { void g() const {} return g; } (f() == f()) ? int : bool x;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Call (@1 (Call (@1 (Type Void)) () ((pure) (const)))) ()
              ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Call (@1 (Type Void)) () ((pure) (const)))) ()
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ())
                      (type_expr
                       ((@1 (Call (@1 (Type Void)) () ((pure) (const))))))
                      (name g)
                      (init_expr
                       ((@1
                         (Lambda (@1 (Type Void)) () ((pure) (const))
                          (@1 (BoundFrame 0 (@1 (Compound ())))) (1))))))
                     (0 1)))
                   (@1 (Return (@1 (BoundIdentifier g (0 1))))))))))
              (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let x = [];";
  [%expect{| Error: @1 cannot infer type of empty array literal |}]

let%expect_test _ =
  evaluate_declarations "let x = [1, 2][1];";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (0 0))) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int[] f() const { mut int[][] a; a = [[0, 0], [0, 0]]; a[0][1] = 1; return a[0]; } let x = f() const;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Index (@1 (Type Int)) ())) () ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Index (@1 (Type Int)) ())) () ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut)))
                      (type_expr
                       ((@1 (Index (@1 (Index (@1 (Type Int)) ())) ()))))
                      (name a)
                      (init_expr
                       ((@1 (DynamicArray () ((@1 (Index (@1 (Type Int)) ()))))))))
                     (0 1)))
                   (@1
                    (Expression
                     (@1
                      (Assignment (@1 (BoundIdentifier a (0 1)))
                       (@1
                        (DynamicArray
                         ((@1
                           (DynamicArray
                            ((@1 (IntLiteral 0)) (@1 (IntLiteral 0)))
                            ((@1 (Type Int)))))
                          (@1
                           (DynamicArray
                            ((@1 (IntLiteral 0)) (@1 (IntLiteral 0)))
                            ((@1 (Type Int))))))
                         ((@1 (Index (@1 (Type Int)) ())))))))))
                   (@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Index
                         (@1
                          (Index (@1 (BoundIdentifier a (0 1)))
                           ((@1 (IntLiteral 0)))))
                         ((@1 (IntLiteral 1)))))
                       (@1 (IntLiteral 1))))))
                   (@1
                    (Return
                     (@1
                      (Index (@1 (BoundIdentifier a (0 1)))
                       ((@1 (IntLiteral 0))))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0)))
           (@1
            (DynamicArray ((@1 (IntLiteral 0)) (@1 (IntLiteral 1)))
             ((@1 (Type Int))))))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "(bool, int) f() const { mut (bool, int) a; a[0] = true; a[1] = 7; return a; } let x = f() const;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1
             (Call (@1 (Tuple ((@1 (Type Bool)) (@1 (Type Int))))) ()
              ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Tuple ((@1 (Type Bool)) (@1 (Type Int))))) ()
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut)))
                      (type_expr
                       ((@1 (Tuple ((@1 (Type Bool)) (@1 (Type Int)))))))
                      (name a)
                      (init_expr
                       ((@1
                         (Tuple ((@1 (BoolLiteral false)) (@1 (IntLiteral 0))))))))
                     (0 1)))
                   (@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Index (@1 (BoundIdentifier a (0 1)))
                         ((@1 (IntLiteral 0)))))
                       (@1 (BoolLiteral true))))))
                   (@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Index (@1 (BoundIdentifier a (0 1)))
                         ((@1 (IntLiteral 1)))))
                       (@1 (IntLiteral 7))))))
                   (@1 (Return (@1 (BoundIdentifier a (0 1))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0)))
           (@1 (Tuple ((@1 (BoolLiteral true)) (@1 (IntLiteral 7))))))))))))
    |}]

(* Type of x is the same as f() but f() cannot be evaluated at compile time *)
let%expect_test _ =
  evaluate_declarations "int f() { return 0; } let x = f();";
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
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0)))
           (@1 (Call (@1 (BoundIdentifier f (0 0))) () ())))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f(int i) const { mut (bool, int) a; a[i] = true; return 0; } let x = f(0);";
  [%expect{| Error: @1 'i' is not a compile-time constant |}]

(* 0+0 index on LHS of assignment is folded to 0 *)
let%expect_test _ =
  evaluate_declarations "int f(int i) const { mut int[] a = [0]; a[0+0] = 0; return a[0]; }";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Int))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name i)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut)))
                      (type_expr ((@1 (Index (@1 (Type Int)) ())))) (name a)
                      (init_expr
                       ((@1
                         (DynamicArray ((@1 (IntLiteral 0))) ((@1 (Type Int))))))))
                     (1 1)))
                   (@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Index (@1 (BoundIdentifier a (1 1)))
                         ((@1 (IntLiteral 0)))))
                       (@1 (IntLiteral 0))))))
                   (@1
                    (Return
                     (@1
                      (Index (@1 (BoundIdentifier a (1 1)))
                       ((@1 (IntLiteral 0))))))))))))
              (0))))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f(int i) const { mut int[] a = [0]; a[i] = 0; return a[i]; } let x = f(0) const;";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Int))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name i)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut)))
                      (type_expr ((@1 (Index (@1 (Type Int)) ())))) (name a)
                      (init_expr
                       ((@1
                         (DynamicArray ((@1 (IntLiteral 0))) ((@1 (Type Int))))))))
                     (1 1)))
                   (@1
                    (Expression
                     (@1
                      (Assignment
                       (@1
                        (Index (@1 (BoundIdentifier a (1 1)))
                         ((@1 (BoundIdentifier i (0 1))))))
                       (@1 (IntLiteral 0))))))
                   (@1
                    (Return
                     (@1
                      (Index (@1 (BoundIdentifier a (1 1)))
                       ((@1 (BoundIdentifier i (0 1)))))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 0)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() const { let a = (1, 2); a[0] = 3; return a[0]; } let x = f() const;";
  [%expect{| Error: @1 cannot assign to immutable variable 'a' |}]

let%expect_test _ =
  evaluate_declarations "int f() const { let a = (1, 2); a[true] = 3; return a[0]; } let x = f() const;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "int f() const { 1[0] = 3; return 0; } let x = f() const;";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "mut int[] a = [0]; type t = typeof(a[1/0] = 7);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut))) (type_expr ((@1 (Index (@1 (Type Int)) ()))))
          (name a)
          (init_expr
           ((@1 (DynamicArray ((@1 (IntLiteral 0))) ((@1 (Type Int))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Int)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let x = [1, 2][3];";
  [%expect{| Error: @1 invalid operation: array index out of bounds: 3 |}]

let%expect_test _ =
  evaluate_declarations "let x = [1, 2][-3];";
  [%expect{| Error: @1 invalid operation: array index out of bounds: -3 |}]

let%expect_test _ =
  evaluate_declarations "let x = 1[3];";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "let x = [1,2][false];";
  [%expect{| Error: @1 type mismatch |}]


let%expect_test _ =
  evaluate_declarations "type t = typeof([1,2]);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Index (@1 (Type Int)) ())))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type t = typeof([1,2][3]);";
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
  evaluate_declarations "type t = typeof(1[3]);";
  [%expect{| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return [int, bool][1]; } f() x;";
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
              (0))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name x)
          (init_expr ((@1 (BoolLiteral false)))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "type f() const { return [int, bool][2]; } f() x;";
  [%expect{| Error: @1 invalid operation: array index out of bounds: 2 |}]

let%expect_test _ =
  evaluate_declarations "int[] a; type t = typeof(a);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Index (@1 (Type Int)) ())))) (name a)
          (init_expr ((@1 (DynamicArray () ((@1 (Type Int))))))))
         (0 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Index (@1 (Type Int)) ())))))
         (1 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int a() { return a(); } let b = a; (a==b ? int : bool) x;";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Call (@1 (Type Int)) () ()))))
          (name a)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int)) () ()
              (@1
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1 (Return (@1 (Call (@1 (BoundIdentifier a (0 0))) () ())))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (1 0)))
           (@1 (BoundIdentifier a (0 0)))))))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Int)))) (name x)
          (init_expr ((@1 (IntLiteral 0)))))
         (2 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let b = a[1];";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (0 0)))
           (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (IntLiteral 2)))))))))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier b) (1 0))) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let b = a[-1];";
  [%expect {| Error: @1 invalid operation: tuple index out of bounds: -1 |}]


let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let b = a[2];";
  [%expect {| Error: @1 invalid operation: tuple index out of bounds: 2 |}]

let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let b = a[true];";
  [%expect {| Error: @1 type mismatch |}]

let%expect_test _ =
  evaluate_declarations "mut int i; let a = (1, 2); let b = a[i];";
  [%expect {| Error: @1 'i' is not a compile-time constant |}]

let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let b = a[];";
  [%expect {| Error: @1 expected an index sub-expression |}]

(* Note how this differs from how typeof handles the type of an index expression on an array. In this case we _do_ check tuple bounds within a typeof. *)
let%expect_test _ =
  evaluate_declarations "let a = (1, 2); let t = typeof(a[2]);";
  [%expect {| Error: @1 invalid operation: tuple index out of bounds: 2 |}]

(* Unlike for an array, the type of a tuple element can depend on the index. *)
let%expect_test _ =
  evaluate_declarations "let a = (1, true); type s = typeof(a[0]); type t = typeof(a[1]);";
  [%expect{|
    (@1
     (OrderIndependent
      ((@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier a) (0 0)))
           (@1 (Tuple ((@1 (IntLiteral 1)) (@1 (BoolLiteral true)))))))))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name s)
          (init_expr ((@1 (Type Int)))))
         (1 0)))
       (@1
        (BoundDeclaration
         ((modifiers ()) (type_expr ((@1 (Type Type)))) (name t)
          (init_expr ((@1 (Type Bool)))))
         (2 0))))))
    |}]


let%expect_test _ =
  evaluate_declarations "let a = (false, true); let t = typeof(a[1/0]);";
  [%expect {| Error: @1 invalid operation: division by zero |}]

let%expect_test _ =
  evaluate_declarations "let a = (); let t = a[0];";
  [%expect {| Error: @1 invalid operation: tuple index out of bounds: 0 |}]

let%expect_test _ =
  evaluate_declarations "mut (int, int) a; let t = a[0];";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ((mut)))
          (type_expr ((@1 (Tuple ((@1 (Type Int)) (@1 (Type Int))))))) (name a)
          (init_expr ((@1 (Tuple ((@1 (IntLiteral 0)) (@1 (IntLiteral 0))))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier t) (1 0)))
           (@1 (Index (@1 (BoundIdentifier a (0 0))) ((@1 (IntLiteral 0))))))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "mut (int, int) a; let t = a[1/0];";
  [%expect {| Error: @1 invalid operation: division by zero |}]

(* Index expressions can only be applied to tuples with arity > 1*)

let%expect_test _ =
  evaluate_declarations "let a = (1); let t = a[0];";
  [%expect {| Error: @1 type mismatch |}]

(* 1+1 folds to 2. x is initialized with literal 2 *)
let%expect_test _ =
  evaluate_declarations "int f(bool p) const { if (p) { return 1+1; } else { return 0; } } let x = f(true) const;";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Bool))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name p)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (If (@1 (BoundIdentifier p (0 1)))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 2)))))))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 0))))))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 2)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f(bool p) const { if (p) { return 1; } else { return 0; } } let x = f(false) const;";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Bool))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Bool)))) (name p)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 1
                (@1
                 (Compound
                  ((@1
                    (If (@1 (BoundIdentifier p (0 1)))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 1)))))))
                     (@1 (Compound ((@1 (Return (@1 (IntLiteral 0))))))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 0)))))))))
    |}]

(* 1-1 folds to 0. x is initialized with literal 2 *)
let%expect_test _ =
  evaluate_declarations "int f(int n) const { mut int i=1-1; do { i=i+1; } while i<n; return i; } let x = f(2) const;";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Int))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name i)
                      (init_expr ((@1 (IntLiteral 0)))))
                     (1 1)))
                   (@1
                    (DoWhile
                     (@1
                      (Compound
                       ((@1
                         (Expression
                          (@1
                           (Assignment (@1 (BoundIdentifier i (1 1)))
                            (@1
                             (BinaryOp Plus (@1 (BoundIdentifier i (1 1)))
                              (@1 (IntLiteral 1)))))))))))
                     (@1
                      (BinaryOp Less (@1 (BoundIdentifier i (1 1)))
                       (@1 (BoundIdentifier n (0 1)))))))
                   (@1 (Return (@1 (BoundIdentifier i (1 1))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 2)))))))))
    |}]

(* body of do-while loop iterates at least once, and x is initialized to literal 1. *)
let%expect_test _ =
  evaluate_declarations "int f(int n) const { mut int i=1-1; do { i=i+1; } while i<n; return i; } let x = f(0) const;";
  [%expect {|
    (@1
     (OrderIndependent
      ((@1
        (BoundDeclaration
         ((modifiers ())
          (type_expr
           ((@1 (Call (@1 (Type Int)) ((@1 (Type Int))) ((pure) (const))))))
          (name f)
          (init_expr
           ((@1
             (Lambda (@1 (Type Int))
              ((@1
                (BoundDeclaration
                 ((modifiers ()) (type_expr ((@1 (Type Int)))) (name n)
                  (init_expr ()))
                 (0 1))))
              ((pure) (const))
              (@1
               (BoundFrame 2
                (@1
                 (Compound
                  ((@1
                    (BoundDeclaration
                     ((modifiers ((mut))) (type_expr ((@1 (Type Int)))) (name i)
                      (init_expr ((@1 (IntLiteral 0)))))
                     (1 1)))
                   (@1
                    (DoWhile
                     (@1
                      (Compound
                       ((@1
                         (Expression
                          (@1
                           (Assignment (@1 (BoundIdentifier i (1 1)))
                            (@1
                             (BinaryOp Plus (@1 (BoundIdentifier i (1 1)))
                              (@1 (IntLiteral 1)))))))))))
                     (@1
                      (BinaryOp Less (@1 (BoundIdentifier i (1 1)))
                       (@1 (BoundIdentifier n (0 1)))))))
                   (@1 (Return (@1 (BoundIdentifier i (1 1))))))))))
              (0))))))
         (0 0)))
       (@1
        (Expression
         (@1
          (Assignment (@1 (BoundLet (Identifier x) (1 0))) (@1 (IntLiteral 1)))))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() const { do { } while true; return 0; } let x = f() const;";
  [%expect {| Error: @1 exceeded maximum number of loop iterations |}]

let%expect_test _ =
  evaluate_declarations "int f() const { return f(); } let x = f() const;";
  [%expect {| Error: @1 exceeded maximum number of loop iterations |}]

(* A function making a const call can enter an infinite loop, even if it is never called externally. *)
let%expect_test _ =
  evaluate_declarations "int f() const { return f() const; }";
  [%expect {| Error: @1 exceeded maximum number of loop iterations |}]

let%expect_test _ =
  evaluate_declarations "int f() const { return f(); }";
  [%expect {|
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
               (BoundFrame 0
                (@1
                 (Compound
                  ((@1 (Return (@1 (Call (@1 (BoundIdentifier f (0 0))) () ())))))))))
              (0))))))
         (0 0))))))
    |}]

let%expect_test _ =
  evaluate_declarations "int f() pure { return 0; } let x = f() const;";
  [%expect {| Error: @1 cannot call non-const lambda at compile time |}]

let%expect_test _ =
  evaluate_declarations "int f(int n) const { return n; } mut int i; let x = f(i) const;";
  [%expect {| Error: @1 'i' is not a compile-time constant |}]
