let%expect_test "it parses identifiers" =
  Common.parse "x";
  [% expect{| [(Expr (Identifier "x"))] |}]
  
let%expect_test "it parses unary operations" =
  Common.parse "-1";
  [% expect{| [(Expr (UnOp (Negate, (Int 1L))))] |}]
  
let%expect_test "it parses binary operations" =
  Common.parse "1+2";
  [% expect{| [(Expr (BinOp (Add, (Int 1L), (Int 2L))))] |}];
  Common.parse "1-2";
  [% expect{| [(Expr (BinOp (Subtract, (Int 1L), (Int 2L))))] |}];
  Common.parse "1*2";
  [% expect{| [(Expr (BinOp (Multiply, (Int 1L), (Int 2L))))] |}];
  Common.parse "1/2";
  [% expect{| [(Expr (BinOp (Divide, (Int 1L), (Int 2L))))] |}]

let%expect_test "it structures the AST according to associativity and precedence of arithmetic operators" =
  Common.parse "1*2*3 + 4/5*6";
  [% expect{|
    [(Expr
        (BinOp (Add,
           (BinOp (Multiply, (BinOp (Multiply, (Int 1L), (Int 2L))), (Int 3L))),
           (BinOp (Multiply, (BinOp (Divide, (Int 4L), (Int 5L))), (Int 6L))))))
      ]
    |}]

let%expect_test "it parses an expression in parentheses" =
  Common.parse "(1+2)";
  [% expect{| [(Expr (BinOp (Add, (Int 1L), (Int 2L))))] |}]

let%expect_test "it parses a tuple" =
  Common.parse "(1, 2)";
  [% expect{| [(Expr (Tuple [(Int 1L); (Int 2L)]))] |}]

let%expect_test "it parses the empty tuple" =
  Common.parse "()";
  [% expect{| [(Expr (Tuple []))] |}]

let%expect_test "it parses assignments" =
  Common.parse "x = 1";
  [% expect{| [(Expr (Assignment (None, (Identifier "x"), (Int 1L))))] |}];
  Common.parse "x = y + 1";
  [% expect{|
    [(Expr
        (Assignment (None, (Identifier "x"),
           (BinOp (Add, (Identifier "y"), (Int 1L))))))
      ]
    |}];
  Common.parse "x += 1";
  [% expect{| [(Expr (Assignment ((Some Add), (Identifier "x"), (Int 1L))))] |}];
  Common.parse "x -= 1";
  [% expect{| [(Expr (Assignment ((Some Subtract), (Identifier "x"), (Int 1L))))] |}];
  Common.parse "x *= 1";
  [% expect{| [(Expr (Assignment ((Some Multiply), (Identifier "x"), (Int 1L))))] |}];
  Common.parse "x /= 1";
  [% expect{| [(Expr (Assignment ((Some Divide), (Identifier "x"), (Int 1L))))] |}]
  
let%expect_test "it parses a function call" =
  Common.parse "f()";
  [% expect{| [(Expr (Call ((Identifier "f"), [])))] |}];
  Common.parse "f(1, 2, 3)";
  [% expect{| [(Expr (Call ((Identifier "f"), [(Int 1L); (Int 2L); (Int 3L)])))] |}]

let%expect_test "it parses a lamda expression" =
  Common.parse "fun (x: int): int -> x + 1";
  [% expect{|
    [(Expr
        (Function ([(@1, "x", (IntT 64))], (Some (IntT 64)),
           (Compound [(Expr (BinOp (Add, (Identifier "x"), (Int 1L))))]))))
      ]
    |}];
  Common.parse "fun (x: int) -> x + 1";
  [% expect{|
    [(Expr
        (Function ([(@1, "x", (IntT 64))], None,
           (Compound [(Expr (BinOp (Add, (Identifier "x"), (Int 1L))))]))))
      ]
    |}]
