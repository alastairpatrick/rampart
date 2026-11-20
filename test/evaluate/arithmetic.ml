let%expect_test "it evaluates integer addition" =
  Common.evaluate "1+2";
  [%expect {| [(Expr (Int 3L))] |}];

