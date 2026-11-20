let%expect_test "it parses a compound statement" =
  Common.parse {|
    {
      x = 1
      y = 2
    }
  |};
  [% expect{|
    [(Compound
        [(Expr (Assignment (None, (Identifier "x"), (Int 1L))));
          (Expr (Assignment (None, (Identifier "y"), (Int 2L))))])
      ]
    |}]

  let%expect_test "it parses a conditional statement" =
  Common.parse {|
    if true {
      x = 1
    } else {
      y = 2
    }
  |};
  [% expect{|
    [(Conditional ((Bool true),
        (Compound [(Expr (Assignment (None, (Identifier "x"), (Int 1L))))]),
        (Compound [(Expr (Assignment (None, (Identifier "y"), (Int 2L))))])))
      ]
    |}]