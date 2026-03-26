open Ast
open Location
open MapAst

let%expect_test _ =
  Sexplib.Sexp.output_hum stdout (Ast.sexp_of_expression (traverse_expression (fun _ -> assert false) (fun (l, e) -> 
  match e with
  | Binary_op (_, a, b) -> l, Binary_op (Minus, a, b)

  | _ -> l, e) (null_location, Binary_op (Plus,
                                 (null_location, Int_literal 1L),
                                 (null_location, Binary_op (Plus,
                                    (null_location, Int_literal 2L),
                                    (null_location, Binary_op (Plus, (null_location, Int_literal 3L), (null_location, Int_literal 4L)))))))));
  [%expect{|
    (@0
     (Binary_op Plus (@0 (Int_literal 1))
      (@0
       (Binary_op Minus (@0 (Int_literal 2))
        (@0 (Binary_op Plus (@0 (Int_literal 3)) (@0 (Int_literal 4))))))))
    |}]

let%expect_test _ =
  Sexplib.Sexp.output_hum stdout (Ast.sexp_of_expression (map_expression (fun _ -> assert false) (fun (l, e) -> 
  match e with
  | Binary_op (_, a, b) -> l, Binary_op (Minus, a, b)

  | _ -> l, e) (null_location, Binary_op (Plus,
                                 (null_location, Int_literal 1L),
                                 (null_location, Binary_op (Plus,
                                    (null_location, Int_literal 2L),
                                    (null_location, Binary_op (Plus, (null_location, Int_literal 3L), (null_location, Int_literal 4L)))))))));
  [%expect{|
    (@0
     (Binary_op Minus (@0 (Int_literal 1))
      (@0
       (Binary_op Minus (@0 (Int_literal 2))
        (@0 (Binary_op Minus (@0 (Int_literal 3)) (@0 (Int_literal 4))))))))
    |}]
