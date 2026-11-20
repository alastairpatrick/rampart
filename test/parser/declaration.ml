let%expect_test "it parses a variable declaration" =
  Common.parse "let x: int = 1";
  [% expect{|
    [(Expr
        (Assignment (None, (Convert ((Let ("x", false)), (IntT 64))), (Int 1L))))
      ]
    |}];
  Common.parse "let x = 1";
  [% expect{| [(Expr (Assignment (None, (Let ("x", false)), (Int 1L))))] |}];
  Common.parse "let x: int";
  [% expect{| [(Expr (Convert ((Let ("x", false)), (IntT 64))))] |}]

let%expect_test "it parses a function declaration" =
  Common.parse {|
    fun f(x: int): int {
      x + 1
    }
  |};
  [% expect{|
    [(Expr
        (Assignment (None, (Let ("f", false)),
           (Function ([(@2, "x", (IntT 64))], (Some (IntT 64)),
              (Compound [(Expr (BinOp (Add, (Identifier "x"), (Int 1L))))])))
           )))
      ]
    |}];
  Common.parse {|
    fun f(x: int) {
      x + 1
    }
  |};
  [% expect{|
    [(Expr
        (Assignment (None, (Let ("f", false)),
           (Function ([(@2, "x", (IntT 64))], None,
              (Compound [(Expr (BinOp (Add, (Identifier "x"), (Int 1L))))])))
           )))
      ]
    |}];
  Common.parse {|
    fun f(x: int) -> x+1
  |};
  [% expect{|
    [(Expr
        (Assignment (None, (Let ("f", false)),
           (Function ([(@2, "x", (IntT 64))], None,
              (Compound [(Expr (BinOp (Add, (Identifier "x"), (Int 1L))))])))
           )))
      ]
    |}]

let%expect_test "it parses a let-in expression" =
  Common.parse "let x: int = 1 in x + 1";
  [% expect{|
    [(Expr
        (In (
           (Assignment (None, (Convert ((Let ("x", false)), (IntT 64))), (
              Int 1L))),
           (BinOp (Add, (Identifier "x"), (Int 1L))))))
      ]
    |}]

(* TODO: test parsing of 'in'-less 'let' declaration *)