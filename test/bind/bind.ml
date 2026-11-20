let%expect_test "it reports a diagnostic on unbound identifier" =
  Common.bind "x";
  [%expect {|
    ERROR line 1, character 1: Identifier 'x' not found
    [(Expr (BoundIdentifier ("x", (-1, -1))))]
    |}]

let%expect_test "it adds a declared identifier to the environment and binds to it" =
  Common.bind {|
    let x = 1
    x
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr (BoundIdentifier ("x", (0, 0))))]
    |}]

let%expect_test "it adds multiple declared identifiers to the environment and binds to them" =
  Common.bind {|
    let x = 1
    let y = 2
    y + x
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr (Assignment (None, (BoundLet ("y", (1, 0))), (Int 2L))));
      (Expr
         (BinOp (Add, (BoundIdentifier ("y", (1, 0))),
            (BoundIdentifier ("x", (0, 0))))))
      ]
    |}]

let%expect_test "it hides the environment of the left hand side of an assignment from the right hand side" =
  Common.bind "let x = x";
  [%expect {|
    ERROR line 1, character 9: Identifier 'x' not found
    [(Expr
        (Assignment (None, (BoundLet ("x", (0, 0))),
           (BoundIdentifier ("x", (-1, -1))))))
      ]
    |}]

let%expect_test "it reports a diagnostic on redeclaration of an identifier in the same scope" =
  Common.bind {|
    let x = 1
    let x = 2
  |};
  [%expect {|
    ERROR line 3, characters 5-9: Identifier 'x' already declared in this scope
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr (Assignment (None, (BoundLet ("x", (-1, -1))), (Int 2L))))]
    |}]

let%expect_test "it permits redeclaration of an identifier in a nested scope and binds to the correct one" =
  Common.bind {|
    let x = 1
    {
      let x = 2
      x
    }
    x
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Compound
         [(Expr (Assignment (None, (BoundLet ("x", (1, 0))), (Int 2L))));
           (Expr (BoundIdentifier ("x", (1, 0))))]);
      (Expr (BoundIdentifier ("x", (0, 0))))]
    |}]

let%expect_test "it reports a diagnostic on redeclaration of an identifier in the same scope after a nested scope" =
  Common.bind {|
    let x = 1
    {
      let x = 2
    }
    let x = 3
  |};
  [%expect {|
    ERROR line 6, characters 5-9: Identifier 'x' already declared in this scope
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Compound [(Expr (Assignment (None, (BoundLet ("x", (1, 0))), (Int 2L))))]);
      (Expr (Assignment (None, (BoundLet ("x", (-1, -1))), (Int 3L))))]
    |}]

let%expect_test "it exposes the environment of the left hand side of an in operator to the right hand side but not to the outer scope" =
  Common.bind {|
    let x = 1 in x + 1
    x
  |};
  [%expect {|
    ERROR line 3, character 5: Identifier 'x' not found
    [(Expr
        (In ((Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))),
           (BinOp (Add, (BoundIdentifier ("x", (0, 0))), (Int 1L))))));
      (Expr (BoundIdentifier ("x", (-1, -1))))]
    |}]

let%expect_test "it begins a new scope for the left hand side of an in expression" =
  Common.bind {|
    let x = 1
    let x = 2 in x+1
    x
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr
         (In ((Assignment (None, (BoundLet ("x", (1, 0))), (Int 2L))),
            (BinOp (Add, (BoundIdentifier ("x", (1, 0))), (Int 1L))))));
      (Expr (BoundIdentifier ("x", (0, 0))))]
    |}]

let%expect_test "it begins a new scope for the right hand side of an in expression and does not expose the left hand side to the outer scope" =
  Common.bind {|
    let y = 2 in
      let y = 3 in y
    y
  |};
  [%expect {|
    ERROR line 4, character 5: Identifier 'y' not found
    [(Expr
        (In ((Assignment (None, (BoundLet ("y", (0, 0))), (Int 2L))),
           (In ((Assignment (None, (BoundLet ("y", (1, 0))), (Int 3L))),
              (BoundIdentifier ("y", (1, 0)))))
           )));
      (Expr (BoundIdentifier ("y", (-1, -1))))]
    |}]

let%expect_test "it allows a mutable identifier to be assigned to" =
  Common.bind {|
    mut x = 1
    x = 2
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr (Assignment (None, (BoundIdentifier ("x", (0, 0))), (Int 2L))))]
    |}]

let%expect_test "it exposes the environment of the left hand side of a convert operator to the surrounding environment" =
  Common.bind {|
    let x = 1
    let y: int = x
    y
  |};
  [%expect {|
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr
         (Assignment (None, (Convert ((BoundLet ("y", (1, 0))), (IntT 64))),
            (BoundIdentifier ("x", (0, 0))))));
      (Expr (BoundIdentifier ("y", (1, 0))))]
    |}]

let%expect_test "it exposes the environment of the left hand side of a convert operator to the right hand side but not to the outer scope" =
  Common.bind {|
    let x = 1
    let y: int = x in y + 1
    y
  |};
  [%expect {|
    ERROR line 4, character 5: Identifier 'y' not found
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr
         (In (
            (Assignment (None, (Convert ((BoundLet ("y", (1, 0))), (IntT 64))),
               (BoundIdentifier ("x", (0, 0))))),
            (BinOp (Add, (BoundIdentifier ("y", (1, 0))), (Int 1L))))));
      (Expr (BoundIdentifier ("y", (-1, -1))))]
    |}]

let%expect_test "it prevents let expressions on the right hand side of an assignment" =
  Common.bind {|
    mut x = 1
    x = let y = 2
  |};
  [%expect {|
    ERROR line 3, characters 9-13: Declaration of identifier 'y' is invalid in this context
    [(Expr (Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))));
      (Expr
         (Assignment (None, (BoundIdentifier ("x", (0, 0))),
            (Assignment (None, (BoundLet ("y", (-1, -1))), (Int 2L))))))
      ]
    |}]

let%expect_test "it prevents declarations on the right hand side of an in operator" =
  Common.bind {|
    let x = 1 in let y = 2
  |};
    [%expect {|
      ERROR line 2, characters 18-22: Declaration of identifier 'y' is invalid in this context
      [(Expr
          (In ((Assignment (None, (BoundLet ("x", (0, 0))), (Int 1L))),
             (Assignment (None, (BoundLet ("y", (-1, -1))), (Int 2L))))))
        ]
      |}]
  
