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
