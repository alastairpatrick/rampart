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

(* Declarations and identifiers *)

let%expect_test _ =
  evaluate_declarations "int x;";
  [% expect{| 0 |}]

let%expect_test _ =
  evaluate_declarations "int x = true;";
  [% expect{|
    Error: @1 type mismatch
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
