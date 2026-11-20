(* White Space *)

let%expect_test "it skips whitespace" =
  Common.parse "  \n  \t  ";
  [% expect{| [] |}]

let%expect_test "it skips line continuation sequence" =
  Common.parse {|
  1 \
  +1
  |};
  [% expect{| [(Expr (BinOp (Add, (Int 1L), (Int 1L))))] |}];
  Common.parse "1 \\\r\n+1";
  [% expect{| [(Expr (BinOp (Add, (Int 1L), (Int 1L))))] |}]  


(*  Comments *)

let%expect_test "it skips single line comments" =
  Common.parse {|
  // this is a comment
  1
  |};
  [% expect{| [(Expr (Int 1L))] |}];
  Common.parse {|
  1 // this is a comment
  |};
  [% expect{| [(Expr (Int 1L))] |}];
  Common.parse "1 // this is a comment\r\n";
  [% expect{| [(Expr (Int 1L))] |}]

let%expect_test "it skips multi-line comments" =
  Common.parse {|
  /* this is a comment */
  1
  |};
  [% expect{| [(Expr (Int 1L))] |}];
  Common.parse {|
  1 /* this is a comment */
  |};
  [% expect{| [(Expr (Int 1L))] |}];
  Common.parse {|
  /*
  this is a comment
  */
  1
  |};
  [% expect{| [(Expr (Int 1L))] |}]

let%expect_test "it skips nested multi-line comments" =
  Common.parse {|
  /*
  /* this is a comment */
  */
  1
  |};
  [% expect{| [(Expr (Int 1L))] |}]

let %expect_test "it outputs a diagnostic on unclosed multi-line comment" =
  Common.parse "/*/**/";
  [% expect{|
    ERROR line 1, character 7: unclosed comment
    []
    |}]


(* Error Recovery *)

let%expect_test "it outputs a diagnostic on unexpected character" =
  Common.parse "\n  @";
  [% expect{|
    ERROR line 2, character 3: unexpected token beginning '@'
    []
    |}]

let%expect_test "it outputs a diagnostic on unexpected non-printable character, escaping that character" =
  Common.parse "\n  \b";
  [% expect{|
    ERROR line 2, character 3: unexpected token beginning '\b'
    []
    |}]

let%expect_test "it recovers from an unexpected character by restarting with the next newline token" =
  Common.parse {|
    1 @ 2
    3
  |};
  [% expect{|
    ERROR line 2, character 7: unexpected token beginning '@'
    [(Expr (Int 1L)); (Expr (Int 3L))]
    |}]

let%expect_test "it skips newlines within nested muilti-line comments during error recovery" =
  Common.parse {|
    1 @ /*/*
    don't recover here!
    */ or here
    */ or here
    2
  |};
  [% expect{|
    ERROR line 2, character 7: unexpected token beginning '@'
    [(Expr (Int 1L)); (Expr (Int 2L))]
    |}]


let%expect_test "it skips newlines associated with line continuation sequences during error recovery" =
  Common.parse {|
    1 @ \
    2 
    3
  |};
  [% expect{|
    ERROR line 2, character 7: unexpected token beginning '@'
    [(Expr (Int 1L)); (Expr (Int 3L))]
    |}]

