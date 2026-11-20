let%expect_test "it binds tuple destructuring" =
  Common.bind {|
    (let a, let b) = (1, 2)
    a
    b
  |};
  [%expect {|
    [(Expr
        (Assignment (None,
           (Tuple [(BoundLet ("a", (0, 0))); (BoundLet ("b", (1, 0)))]),
           (Tuple [(Int 1L); (Int 2L)]))));
      (Expr (BoundIdentifier ("a", (0, 0))));
      (Expr (BoundIdentifier ("b", (1, 0))))]
    |}]


let%expect_test "it prevents an identifier declared in a tuple destructuring from being bound before it is initialized" =
  Common.bind {|
    (let a, let b = a) = (1, 2)
    a
  |};
  [%expect {|
    ERROR line 2, characters 13-21: This expression may not appear on the left hand side of an assignment
    [(Expr
        (Assignment (None,
           (Tuple
              [(BoundLet ("a", (0, 0)));
                (Assignment (None, (Let ("b", false)), (Identifier "a")))]),
           (Tuple [(Int 1L); (Int 2L)]))));
      (Expr (BoundIdentifier ("a", (0, 0))))]
    |}]

(*
This snippet below should cause a diagnostic error. However, it will be the static type checking pass that catches it, rather than the binding pass.

let%expect_test "it prevents an identifier declared in a tuple destructuring from being assigned to other than through initialization" =
  Common.bind {|
    (let a, let b) = (1, 2)
    a = 3
    b = 4
  |};
  [%expect {|
    ERROR line 3, character 5: Immutable identifier 'a' cannot be assigned to
    ERROR line 4, character 5: Immutable identifier 'b' cannot be assigned to
    [(Expr
        (Assignment (None,
           (Tuple [(BoundLet ("a", (0, 0))); (BoundLet ("b", (1, 0)))]),
           (Tuple [(Int 1L); (Int 2L)]))));
      (Expr (Assignment (None, (BoundIdentifier ("a", (0, 0))), (Int 3L))));
      (Expr (Assignment (None, (BoundIdentifier ("b", (1, 0))), (Int 4L))))]
    |}]
*)