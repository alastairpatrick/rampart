open Bind
open Const
open Diagnostic
open Error
open LowerLambda
open LexPass
open Location
open Recovery


let evaluate_declarations text =
  dangerously_reset_distinct_closure_identity();
  try
    let lexbuf = Lexing.from_string text in
    let tokens = lex_pass lexbuf in
    let statement = parse_recovering (make_diagnostic_sink ()) tokens in
    let env = top_scope () in
    let num_globals, statement = bind_program env statement in
    let program = lower_lambda_pass statement num_globals in
    Sexplib.Sexp.output_hum stdout (Ast.sexp_of_statement program)
  with Located_error (location, message) -> Printf.printf "Error: %s %s\n" (show_location location) message

(* adds closure parameter to lambda expression *)
let%expect_test _ =
  evaluate_declarations "int&(int x) -> x;";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda (Unevaluated (@1 (Type Int)))
           ((@1
             (Bound_declaration
              ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name x)
               (init_expr ()))
              (0 1)))
            (@1
             (Bound_declaration
              ((modifiers ()) (typ (Pointer Opaque)) (name $closure)
               (init_expr ()))
              (1 1))))
           () (@1 (Bound_frame 2 (@1 (Return (@1 (Bound_identifier x (0 1))))))))))))))
    |}]

(* descends into nested nested lambdas *)
let%expect_test _ =
  evaluate_declarations "(int<-(int)) & () -> (int&(int x) -> x);";
  [% expect{|
    (@1
     (Order_independent
      ((@1
        (Expression
         (@1
          (Lambda
           (Unevaluated
            (@1
             (Type
              (Function (Unevaluated (@1 (Type Int)))
               ((Unevaluated (@1 (Type Int)))) ()))))
           ((@1
             (Bound_declaration
              ((modifiers ()) (typ (Pointer Opaque)) (name $closure)
               (init_expr ()))
              (0 1))))
           ()
           (@1
            (Bound_frame 1
             (@1
              (Return
               (@1
                (Lambda (Unevaluated (@1 (Type Int)))
                 ((@1
                   (Bound_declaration
                    ((modifiers ()) (typ (Unevaluated (@1 (Type Int)))) (name x)
                     (init_expr ()))
                    (0 2)))
                  (@1
                   (Bound_declaration
                    ((modifiers ()) (typ (Pointer Opaque)) (name $closure)
                     (init_expr ()))
                    (1 2))))
                 ()
                 (@1
                  (Bound_frame 2 (@1 (Return (@1 (Bound_identifier x (0 2))))))))))))))))))))
    |}]