let%expect_test "it binds an addition expression" =
  Common.bind "1+2";
  [%expect {| [(Expr (BinOp (Add, (Int 1L), (Int 2L))))] |}]

let%expect_test "it does not allow declarations within a unary expression" =
  Common.bind {|
    - (let x=1)
    x
  |};
  [%expect {|
    ERROR line 2, characters 8-12: Declaration of identifier 'x' is invalid in this context
    ERROR line 3, character 5: Identifier 'x' not found
    [(Expr
        (UnOp (Negate, (Assignment (None, (BoundLet ("x", (-1, -1))), (Int 1L)))
           )));
      (Expr (BoundIdentifier ("x", (-1, -1))))]
    |}]

let%expect_test "it does not allow declarations within a binary expression" =
  Common.bind {|
    (let x=1) + (let y=2)
    x
    y
  |};
  [%expect {|
    ERROR line 2, characters 6-10: Declaration of identifier 'x' is invalid in this context
    ERROR line 2, characters 18-22: Declaration of identifier 'y' is invalid in this context
    ERROR line 3, character 5: Identifier 'x' not found
    ERROR line 4, character 5: Identifier 'y' not found
    [(Expr
        (BinOp (Add, (Assignment (None, (BoundLet ("x", (-1, -1))), (Int 1L))),
           (Assignment (None, (BoundLet ("y", (-1, -1))), (Int 2L))))));
      (Expr (BoundIdentifier ("x", (-1, -1))));
      (Expr (BoundIdentifier ("y", (-1, -1))))]
    |}]

let%expect_test "it allows a declaration within an in expression, regardless of surrounding context" =
  Common.bind {|
    1 + (let x=1 in x+1)
  |};
  [%expect {|
    [(Expr
        (BinOp (Add, (Int 1L),
           (In ((Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))),
              (BinOp (Add, (BoundIdentifier ("x", (0, 0))), (Int 1L)))))
           )))
      ]
    |}]