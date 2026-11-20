let%expect_test "it adds the parameters of a function to the environment and allows them to be bound to" =
  Common.bind {|
    fun f(x: int, y: int): int -> x + y
  |};
  [%expect {|
    [(Expr
        (Assignment (None, (BoundLet ("f", (0, 0))),
           (Function ([(@2, "x", (IntT 64)); (@2, "y", (IntT 64))],
              (Some (IntT 64)),
              (Compound
                 [(Expr
                     (BinOp (Add, (BoundIdentifier ("x", (0, 1))),
                        (BoundIdentifier ("y", (1, 1))))))
                   ])
              ))
           )))
      ]
    |}]

let%expect_test "it prevents multiple parameters with the same name from being declared" =
  Common.bind {|
    fun f(x: int, x: int): int -> x
  |};
  [%expect {|
    ERROR line 2, characters 19-24: Parameter 'x' redeclared
    [(Expr
        (Assignment (None, (BoundLet ("f", (0, 0))),
           (Function ([(@2, "x", (IntT 64)); (@2, "x", (IntT 64))],
              (Some (IntT 64)),
              (Compound [(Expr (BoundIdentifier ("x", (0, 1))))])))
           )))
      ]
    |}]

let%expect_test "it treats parameters and local variables as separate scopes" =
  Common.bind {|
    fun f(x: int): int {
      let x = 1
      x
    }
  |};
  [%expect {|
    [(Expr
        (Assignment (None, (BoundLet ("f", (0, 0))),
           (Function ([(@2, "x", (IntT 64))], (Some (IntT 64)),
              (Compound
                 [(Expr (Assignment (None, (BoundLet ("x", (1, 1))), (Int 1L))));
                   (Expr (BoundIdentifier ("x", (1, 1))))])
              ))
           )))
      ]
    |}]
    
let%expect_test "it does not allow declarations within argument expressions" =
  Common.bind {|
    fun f(x: int): int -> x
    f(let x=1)
  |};
  [%expect {|
    ERROR line 3, characters 7-11: Declaration of identifier 'x' is invalid in this context
    [(Expr
        (Assignment (None, (BoundLet ("f", (0, 0))),
           (Function ([(@2, "x", (IntT 64))], (Some (IntT 64)),
              (Compound [(Expr (BoundIdentifier ("x", (0, 1))))])))
           )));
      (Expr
         (Call ((BoundIdentifier ("f", (0, 0))),
            [(Assignment (None, (BoundLet ("x", (-1, -1))), (Int 1L)))])))
      ]
    |}]

let%expect_test "it does not allow declarations within an expression evaluating to the callee of a call" =
  Common.bind {|
    fun f(x: int): int -> x
    (let g=f)(1)
  |};
  [%expect {|
    ERROR line 3, characters 6-10: Declaration of identifier 'g' is invalid in this context
    [(Expr
        (Assignment (None, (BoundLet ("f", (0, 0))),
           (Function ([(@2, "x", (IntT 64))], (Some (IntT 64)),
              (Compound [(Expr (BoundIdentifier ("x", (0, 1))))])))
           )));
      (Expr
         (Call (
            (Assignment (None, (BoundLet ("g", (-1, -1))),
               (BoundIdentifier ("f", (0, 0))))),
            [(Int 1L)])))
      ]
    |}]

