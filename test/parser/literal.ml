let%expect_test "it parses boolean literals" =
  Common.parse "true";
  [% expect{| [(Expr (Bool true))] |}];
  Common.parse "false";
  [% expect{| [(Expr (Bool false))] |}]

let%expect_test "it parses a decimal integer literal" =
  Common.parse "12345";
  [% expect{| [(Expr (Int 12345L))] |}]

let%expect_test "it parses a hexadecimal integer literal" =
  Common.parse "0xABCD";
  [% expect{| [(Expr (Int 43981L))] |}];
  Common.parse "0Xabcd";
  [% expect{| [(Expr (Int 43981L))] |}]

let%expect_test "it parses a binary integer literal" =
  Common.parse "0b11000000111001";
  [% expect{| [(Expr (Int 12345L))] |}];
  Common.parse "0B11000000111001";
  [% expect{| [(Expr (Int 12345L))] |}]

let%expect_test "it parses an octal integer literal" =
  Common.parse "0o30071";
  [% expect{| [(Expr (Int 12345L))] |}];
  Common.parse "0O30071";
  [% expect{| [(Expr (Int 12345L))] |}]

let%expect_test "it parses an integer literal >= 2^63 and represents it as a negative int64" =
  Common.parse "0xFFFFFFFFFFFFFFFF";
  [% expect{| [(Expr (Int -1L))] |}]
