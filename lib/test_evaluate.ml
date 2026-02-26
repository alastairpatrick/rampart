open Bind
open Diagnostic
open Evaluate
open LexPass
open Recovery
open Value

let evaluate_declarations text =
  let lexbuf = Lexing.from_string text in
  let tokens = lex_pass lexbuf in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    let env = top_scope () in
    let num_variables, statement = bind_program env statement in
    let machine = make_machine num_variables in
    evaluate_program machine statement;
    for i = 0 to num_variables-1 do
      print_endline (show_value machine.globals.(i))
    done

(* Arithmetic *)

let%expect_test _ =
  evaluate_declarations "int x = 1 + 2;";
  [% expect{| 3 |}]

let%expect_test _ =
  evaluate_declarations "int x = 6/2;";
  [% expect{| 3 |}]

let%expect_test _ =
  evaluate_declarations "int x = 6/0;";
  [% expect{|
    Division_by_zero
    [:failed:]
    |}]

(* Defer / dependency resume behavior *)

let%expect_test _ =
  evaluate_declarations "int x = y + 1; int y = 10;";
  [% expect{|
    11
    10
    |}]

(* Declarations and identifiers *)

let%expect_test _ =
  evaluate_declarations "int x;";
  [% expect{| 0 |}]

let%expect_test _ =
  evaluate_declarations "int x = true;";
  [% expect{|
    Error: @1 no implicit conversion from 'bool' to 'int'
    [:failed:]
    |}]

let%expect_test _ =
  evaluate_declarations "int x=y+1; int y;";
  [% expect{|
    1
    0
    |}]

let%expect_test _ =
  evaluate_declarations "let x=y+1; int y;";
  [% expect{|
    1
    0
    |}]

let%expect_test _ =
  evaluate_declarations "let x = (z+1, z+2); int z = 5;";
  [% expect{|
    (6,7)
    5
    |}]

let%expect_test _ =
  evaluate_declarations "(let x, let y) = (z+1, z+2); int z = 5;";
  [% expect{|
    6
    7
    5
    |}]

let%expect_test _ =
  evaluate_declarations "((let x), let y) = (z+1, z+2); int z = 5;";
  [% expect{|
    6
    7
    5
    |}]

let%expect_test _ =
  evaluate_declarations "() = ();";
  [% expect{|
    |}]

let%expect_test _ =
  evaluate_declarations "(let x, let y) = (z+1, z+2, z+3); int z = 5;";
  [% expect{|
    Error: @1 type mismatch
    [:uninitialized:]
    [:uninitialized:]
    5
    |}]

let%expect_test _ =
  evaluate_declarations "(let x, let y) = z+1; int z = 5;";
  [% expect{|
    Error: @1 type mismatch
    [:uninitialized:]
    [:uninitialized:]
    5
    |}]

let%expect_test _ =
  evaluate_declarations "(let x, let y) = z; (int, int) z;";
  [% expect{|
    0
    0
    (0,0)
    |}]

let%expect_test _ =
  evaluate_declarations "int x = y; int y = x;";
  [% expect{|
    Cyclic dependencies detected: x, y
    [:uninitialized:]
    [:uninitialized:]
    |}]

let%expect_test _ =
  evaluate_declarations "int x = let y = 2 in y + 3;";
  [% expect{|
    5
    2
    |}]

let%expect_test _ =
  evaluate_declarations "int x = let y = 2 in y + z; int z = 3;";
  [% expect{|
    5
    3
    2
    |}]

let%expect_test _ =
  evaluate_declarations "void foo(int x) {}";
  [% expect{| [:impl void(int):] |}]

(* arity *)

let%expect_test _ =
  evaluate_declarations "int x = arity(());";
  [% expect{|
    0
    |}]

let%expect_test _ =
  evaluate_declarations "int x = arity(int);";
  [% expect{|
    1
    |}]

let%expect_test _ =
  evaluate_declarations "int x = arity((int, int));";
  [% expect{|
    2
    |}]

let%expect_test _ =
  evaluate_declarations "int x = arity(7);";
  [% expect{|
    1
    |}]

let%expect_test _ =
  evaluate_declarations "type x = bool;";
  [% expect{|
    bool
    |}]

(* typeof *)

let%expect_test _ =
  evaluate_declarations "let t = typeof(1);";
  [% expect{| int |}]

let%expect_test _ =
  evaluate_declarations "let t = typeof(1/0);";
  [% expect{| int |}]

let%expect_test _ =
  evaluate_declarations "let t = typeof(x); int x;";
  [% expect{|
    int
    0
    |}]

let%expect_test _ =
  evaluate_declarations "int x = 1; let t = typeof(x = 2);";
  [% expect{|
    1
    int
    |}]

let%expect_test _ =
  evaluate_declarations "let t = typeof(() = (1, 2));";
  [% expect{|
    Error: @1 type mismatch
    [:uninitialized:]
    |}]

let%expect_test _ =
  evaluate_declarations "typeof(y) x = 3; int y = 4;";
  [% expect{|
    3
    4
    |}]

let%expect_test _ =
  evaluate_declarations "int x = arity(typeof(x));";
  [% expect{|
    1
    |}]

let%expect_test _ =
  evaluate_declarations "int x = arity(typeof(x + 1));";
  [% expect{|
    1
    |}]

let%expect_test _ =
  evaluate_declarations "type x = y; typeof(x) y = int;";
  [% expect{|
    int
    int
    |}]

(* implicit type conversions *)

(* Not an actual conversion but rather the trivial case *)
let%expect_test _ =
  evaluate_declarations "int i = 1;";
  [% expect{| 1 |}]

let%expect_test _ =
  evaluate_declarations "type t = (int, bool); t x = (1, true);";
  [% expect{|
    (int, bool)
    (1,true)
    |}]

let%expect_test _ =
  evaluate_declarations "type t = 2;";
  [% expect{|
    Error: @1 type mismatch
    [:failed:]
    |}]

let%expect_test _ =
  evaluate_declarations "(type, type) t = (int, int); t x = (1, 2);";
  [% expect{|
    (int,int)
    (1,2)
    |}]

let%expect_test _ =
  evaluate_declarations "(type, type) t = (int, (bool, int)); type s = t;";
  [% expect{|
    (int,(bool, int))
    (int, (bool, int))
    |}]

let%expect_test _ =
  evaluate_declarations "(type, type, type) t = (bool, int);";
  [% expect{|
    Error: @1 type mismatch
    [:failed:]
    |}]

let%expect_test _ =
  evaluate_declarations "type t = (int, bool); (type, type) s = t;";
  [% expect{|
    (int, bool)
    (int,bool)
    |}]

let%expect_test _ =
  evaluate_declarations "type t = (int, bool); (type, int) s = t;";
  [% expect{|
    Error: @1 no implicit conversion from 'type' to 'int'
    (int, bool)
    [:failed:]
    |}]

let%expect_test _ =
  evaluate_declarations "type t = (int, bool); type s = typeof(t); int a = arity(t);";
  [% expect{|
    (int, bool)
    type
    1
    |}]

let%expect_test _ =
  evaluate_declarations "type s = typeof((int, bool)); int a = arity((int, bool));";
  [% expect{|
    (type, type)
    2
    |}]

(* Functions *)

let%expect_test _ =
  evaluate_declarations "int foo() { return 7; } int x = foo();";
  [% expect{|
    [:impl int():]
    7
    |}] 

let%expect_test _ =
  evaluate_declarations "int a; void foo() { a=7; } foo();";
  [% expect{|
    7
    [:impl void():]
    |}] 

let%expect_test _ =
  evaluate_declarations "int add(int a, int b) { return a+b; } int x = add(3, 4);";
  [% expect{|
    [:impl int(int,int):]
    7
    |}] 

let%expect_test _ =
  evaluate_declarations "int a = 2; int add(int b) { return a+b; } int x = add(3);";
  [% expect{|
    2
    [:impl int(int):]
    5
    |}] 

let%expect_test _ =
  evaluate_declarations "int a = 2; int add(int b) { a = a+1; return a+b; } int x = add(3);";
  [% expect{|
    3
    [:impl int(int):]
    6
    |}] 

let%expect_test _ =
  evaluate_declarations "int foo() {} int x = foo();";
  [% expect{| 
    [:impl int():]
    0
    |}]

let%expect_test _ =
  evaluate_declarations "int foo() { return; } int x = foo();";
  [% expect{|
    Error: @1 no implicit conversion from 'void' to 'int'
    [:impl int():]
    [:failed:]
    |}]

let%expect_test _ =
  evaluate_declarations "(int, int) pair() { return (1, 2); } (int, int) p = pair();";
  [% expect{|
    [:impl (int, int)():]
    (1,2)
    |}]

let%expect_test _ =
  evaluate_declarations "int foo() { int x; return x; } int y = foo();";
  [% expect{|
    [:impl int():]
    0
    |}]


let%expect_test _ =
  evaluate_declarations "int f() { return 7; } let g = f; int i = g();";
  [% expect{|
    [:impl int():]
    [:impl int():]
    7
    |}]

let%expect_test _ =
  evaluate_declarations "int f() { return 7; } int g(int() h) { return h(); } int i = g(f);";
  [% expect{|
    [:impl int():]
    [:impl int(int()):]
    7
    |}]

let%expect_test _ =
  evaluate_declarations "int f(int x) { return x; } int g(int(int) h) { return h(1); } int i = g(f);";
  [% expect{|
    [:impl int(int):]
    [:impl int(int(int)):]
    1
    |}]

let%expect_test _ =
  evaluate_declarations "int(int) make_adder(int b) { int adder(int a) { return a+b; } return adder; } int(int) add2 = make_adder(2); int x = add2(3);";
  [% expect{|
    [:impl int(int)(int):]
    [:impl int(int):]
    5
    |}]

let%expect_test _ =
  evaluate_declarations "2();";
  [% expect{| Error: @1 not callable |}]


let%expect_test _ =
  evaluate_declarations "bool called = false; int f() { called = true; } type t = typeof(f());";
  [% expect{|
    false
    [:impl int():]
    int
    |}]

