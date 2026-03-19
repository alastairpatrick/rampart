(* Big-step interpreter to resolve compile-time constant expressions (CTCE) *)

open Ast
open Bind
open Const
open Error
open Location
open MapAst
open Slot

(* Where possible, prefer to recover from errors in this pass, relying on a later pass to report them. Exceptions:
  - It's okay to raise exceptions that will be caught within this module, such as Saw_uninitialized.
  - Raise internal errors any time something "impossible" happens, for example if we encounter an AST node that we forgot to implement a case for. This is primarily to make it easier to detect and fix bugs in this module. Prefer these to assertions.
  - Located_errors wrapping exceptions that this module must raise anyway is fine.
  - Raise an Error exception when recovery is not practical.
*)

exception Saw_uninitialized of string
exception Return_exn of expression
exception No_match_exn

type value =
| Uninitialized_of_type of (* expression_type: *) expression option
| Const_of_value of expression
| Non_const_of_type of expression

type variable = {
  value: value;
}

type assignable = (* array_idx: *) int * variable array

let empty_variable = { value = Uninitialized_of_type None }

type frame = {
  depth: int;
  enclosing_frame: frame option;
  variables: variable array;
  return_type: expression;
  pure: bool;
  const: bool;
}

type external_closure +=
  | Closure of frame * (* ast_alias: *) expression option

type eval_mode =
  | Fold_consts                   (* Transforms from one AST to another, using Evaluate_const to evaluate the constant type of all declaration types, while performing constant folding. *)
  | Evaluate_type                 (* Evaluate the type of an expression without causing side-effects. Returns a type representative rather than the type itself. Not used on statements. *)
  | Evaluate_const                (* Compile-time evaluation of constant expressions *)

type evaluation_ast =
  | Const
  | Non_const of (* ast: *) expression

type evaluation = evaluation_ast * (* const_value: *) expression

let ast_of (evaluation : evaluation) : expression =
  match evaluation with
  | Const, const_value -> const_value
  | Non_const ast, _ -> ast

let representative_value_of (evaluation : evaluation) : expression =
  match evaluation with
  | Const, const_value -> const_value
  | Non_const _, representative_value -> representative_value

(* Conservative count of loop iterations. Currently counts all calls as potential iterations. *)
let loop_count = ref 0
let evaluate_const_count = ref 0

let increment_loop_count () =
  loop_count := !loop_count + 1;
  if !loop_count > 1000 then raise (Error "exceeded maximum number of loop iterations")

let make_global_frame (num_globals : int) : frame = {
  depth = 0;
  enclosing_frame = None;
  variables = Array.make num_globals empty_variable;
  return_type = (null_location, Type Void);
  pure = false;
  const = false;
}

let rec get_assignable (frame : frame) ({index; depth; mut}: slot) : assignable =
  if depth = frame.depth then
    index, frame.variables
  else begin
    match frame.enclosing_frame with
    | Some enclosing -> get_assignable enclosing {index; depth; mut}
    | None -> raise (error_internal "invalid slot depth")
  end

let get_assignable_value (index, variables) : value = 
  variables.(index).value

let set_assignable_value (index, variables) (value : value) : unit =
  variables.(index) <- { value }

(* Always use this function instead of directly constructing Const_of_value. *)
let check_is_const_value (expression : expression) : value =
  if (is_const_value expression) then begin
    if (const_value_exists (fun e -> match e with (_, Lambda (_, _, _, _, Some (_, Closure (_, None)))) -> true | _ -> false) expression) then
      raise (error_internal "unexpected const value containing a lambda with a closure that has no ast alias");
    Const_of_value expression
  end else
    raise (error_internal (Printf.sprintf "expected const value, got: %s" (Ast.show_expression expression)))


let rec evaluate_statements env frame mode (statements : statement list) : statement list =
  List.map (evaluate_statement env frame mode) statements

and evaluate_order_independent env frame mode statements =
  (* `in_queue` uses a placeholder display name so it has the same pair shape
    as `stalled_queue`.  *)
  let in_queue = Queue.of_seq (Seq.map (fun s -> (s, "")) (List.to_seq statements)) in
  let stalled_queue = Queue.create () in
  let out_queue = Queue.create() in
  let progress_made = ref false in
  while not (Queue.is_empty in_queue) do
    while not (Queue.is_empty in_queue) do
      let (statement, _) = Queue.take in_queue in
      match evaluate_statement env frame mode statement with
      | exception Saw_uninitialized display_name ->
        Queue.add (statement, display_name) stalled_queue;

      | evaluated_statement ->
        progress_made := true;
        Queue.add evaluated_statement out_queue
    done;

    if not !progress_made then begin
      match List.of_seq (Queue.to_seq stalled_queue) with
        | [] -> raise (error_internal "a dependency cycle with no nodes should be impossible");
        | head :: tail ->
          let display_name (_, n) = n in
          let location_of ((l, _), _) = l in
          let msg = Printf.sprintf "found cyclic dependency: %s -> %s"
            (String.concat " -> " (List.map display_name (head::tail)))
            (display_name head)
          in
          raise (Located_error (location_of(head), msg))
    end;

    Queue.transfer stalled_queue in_queue;
    progress_made := false
  done;
  List.of_seq (Queue.to_seq out_queue)

and evaluate_statement (env : env) (frame : frame) (mode : eval_mode) ((location, statement): statement) : statement =
  try
    match statement with
    | Expression expression -> (location, Expression (substitute_lambda_aliases (evaluate_expression env frame mode expression)))
    | Compound statements -> (location, Compound (evaluate_statements env frame mode statements))
    | OrderIndependent statements -> (location, OrderIndependent (evaluate_order_independent env frame mode statements))
    | BoundDeclaration (declaration, slot) -> (location, evaluate_declaration env frame mode location declaration slot)
    | If (condition, consequent, alternative) -> evaluate_if env frame mode location condition consequent alternative
    | DoWhile (body, condition) -> evaluate_do_while env frame mode location body condition  
    | Return e -> (location, Return (substitute_lambda_aliases (evaluate_return env frame mode location e)))
    | _ -> print_endline (Printf.sprintf "statement not implemented: %s" (Ast.show_statement (location, statement))); assert false;
  with Error message -> raise (Located_error (location, message))

(* Always enter Evaluate_const mode using this function or evaluate_const_protect. *)
and evaluate_const_value env frame expression : expression =
  evaluate_const_protect (fun () -> evaluate_expression env frame Evaluate_const expression)

and evaluate_const_protect f =
  evaluate_const_count := !evaluate_const_count + 1;
  Fun.protect
    ~finally: (fun () ->
      evaluate_const_count := !evaluate_const_count - 1;
      if !evaluate_const_count = 0 then loop_count := 0
      )
    f

(* TODO: incrementally move expression evaluation to the new design, then rename this to 'evaluate_expression' and
   remove the old 'evaluate_expression' function. *)
and evaluate_expression_new env frame mode ((location, expression) : expression) : evaluation =
  let result = match expression with
  | IntLiteral _
  | BoolLiteral _
  | Type _ -> Const, (location, expression)

  | BoundIdentifier (display_name, slot) -> evaluate_identifier env frame mode location display_name slot
  | UnaryOp (op, e) -> evaluate_unary_op env frame mode location op e

  | _ -> let result = evaluate_expression env frame mode (location, expression) in
    (* This logic awkwardly makes an evaluation from returned expression. It will go away once all
       expression evaluation has been incrementally moved to the new design. *)
    if is_const_value result then
      Const, result
    else begin
      assert (mode = Fold_consts); (* Both other modes would return a const value *)

      (* Evaluating an expression with evaluate_expression in Fold_consts mode does not retain
         the type. Evaluate a second time in Evaluate_type mode to get the type.
         
         We must be very careful because evaluate_expression_new and evaluate_expression are
         mutually recursive. The case where an infinite recursion occurs is when there is an
         AST node type that neither function handles. Reviewers: ensure that this remains true.
         
         The long term solution is to finish the refactor, which will eliminate this mutual
         recursion. *)
      (Non_const result), evaluate_expression env frame Evaluate_type (location, expression)
    end
  in
   match result with
    | (Non_const ast), _ when mode <> Fold_consts -> raise (error_internal (Printf.sprintf "unexpectedly returned a non-const evaluation %s" (Ast.show_expression ast)))
    | result -> result

and evaluate_expression env frame mode ((location, expression): expression) : expression =
  match expression with
  | BoundLet _ -> raise (Error "'let' expressions may only appear to the left of an assignment")
  | BinaryOp (op, a, b) -> evaluate_binary_op env frame mode location op a b
  | Conditional (condition, consequent, alternative) -> evaluate_conditional env frame mode location condition consequent alternative
  | Fall_through (a, b) -> evaluate_fall_through env frame mode location a b
  | Match (pattern, value, condition, body, temp_slot) -> evaluate_match env frame mode location pattern value condition body temp_slot
  | Assignment (a, b) -> evaluate_assignment env frame mode location a b
  | In (a, b) -> evaluate_in env frame mode location a b
  | Call (callee, args, modifiers) -> evaluate_call env frame mode location callee args modifiers
  | Tuple elements -> evaluate_tuple env frame mode location elements
  | Arity e -> evaluate_arity env frame mode location e
  | DynamicArray (elements, element_type) -> evaluate_dynamic_array_literal env frame mode location elements element_type
  | Index (array, index) -> evaluate_index env frame mode location array index
  | Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), closure) ->
    evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statement closure
  | TypeOf e -> evaluate_typeof env frame mode location e
  | Statement s -> evaluate_expression_statement env frame mode location s
  | _ ->
    let result = evaluate_expression_new env frame mode (location, expression) in
    (* This logic awkwardly makes an expression from an evaluation. It will go away once all
       expression evaluation has been incrementally moved to the new design. *)
    match mode, result with
    | Fold_consts, _ -> ast_of result
    | Evaluate_type, _ -> representative_value_of result
    | Evaluate_const, (Const, const_value) -> const_value
    | _ -> assert false (* Should not reach here in Evaluate_const mode because that mode egerly raises error_not_a_compile_time_constant rather than returning non-const. *)

and evaluate_expression_opt env frame mode (expr_opt : expression option) : expression option =
  match expr_opt with
  | Some expr -> Some (evaluate_expression env frame mode expr)
  | None -> None

and substitute_lambda_aliases expression : expression =
  let helper = function
  | (_, Lambda (_, _, _, _, Some (_, Closure (_, Some ast_alias)))) -> ast_alias
  | expression -> expression in
  map_expression Fun.id helper expression

(* Expression evaluation guidelines.

Fold_consts:
- This mode takes an AST for a program as input and produces an AST for a program as output, one suitable
  for conventional static type checking.
- Walk the AST and reduce constant sub-expressions where possible, even when the surrounding expression
  cannot be fully reduced.
- In particular, normalize certain singleton-typed CTCEs (e.g. `int`, `bool`, and `type`) to their canonical
  constant representations so later passes can treat them as constant values.
- Resolve declaration *types* to constant values by shunting their type expressions through Evaluate_const.
- Avoid doing extra type checking or evaluation that isn't required to produce those constant values.

Evaluate_type:
- This mode reduces an input expression to a representative (and constant) value that has the same
  type as the input expression and can be used in its place for type-checking purposes.
- Since this mode replaces expressions with representative values, it must be careful to type check
  expressions before they are erased.
- The concrete value returned is not meaningful beyond its type; it is only used for type-checking.
- Do not perform side effects or evaluate non-const subexpressions.

Evaluate_const:
- This mode evaluates an expression as a compile-time constant: it must either produce a constant value or raise a diagnostic.
- Evaluation follows the language semantics, including control-flow effects such as short-circuiting and conditional execution.
- Side effects are allowed only when they remain within the compile-time context (e.g. assignment to a local `mut` variable in a const lambda).
- It must not access non-const captured variables, call non-const lambdas, or otherwise depend on runtime-only state.
- Always return a constant value or raise an error; never return an unreduced non-constant expression.
*)


and evaluate_identifier _ frame mode location display_name ({index; depth; mut} : slot) : evaluation =
  let assignable = get_assignable frame {index; depth; mut} in
  begin match get_assignable_value assignable with
  | Uninitialized_of_type None -> raise (Saw_uninitialized display_name)
  | Uninitialized_of_type (Some typ) ->
    if mode = Evaluate_type then
      Const, representative_value_of_type typ
    else
      raise (Saw_uninitialized display_name)
  | Const_of_value const_value ->
    if mut && (not frame.const || depth <> frame.depth) then
      raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name);
    Const, const_value
  | Non_const_of_type typ ->
    match mode with
    | Fold_consts -> Non_const (location, BoundIdentifier (display_name, {index; depth; mut})),
                                          representative_value_of_type typ
    | Evaluate_type -> Const, representative_value_of_type typ (* This might look strange, but all representative values are const values *)
    | Evaluate_const -> raise (error_not_a_compile_time_constant display_name)
  end

and evaluate_logical_op env frame mode location op a b =
  let is_bool expression =
    let expression = evaluate_expression env frame Evaluate_type expression in
    match expression with
    | _, BoolLiteral _ -> true
    | _ -> false
  in
  let a = evaluate_expression env frame mode a in
  match mode with
  | Fold_consts ->
    let b = evaluate_expression env frame mode b in
    begin match op, a, b with
    | LogicalAnd, (_, BoolLiteral false), _ when is_bool b -> a
    | LogicalAnd, (_, BoolLiteral true), _ when is_bool b -> b
    | LogicalAnd, _, (_, BoolLiteral false) when is_bool a -> b
    | LogicalAnd, _, (_, BoolLiteral true) when is_bool a -> a

    | LogicalOr, (_, BoolLiteral false), _ when is_bool b -> b
    | LogicalOr, (_, BoolLiteral true), _ when is_bool b -> a
    | LogicalOr, _, (_, BoolLiteral false) when is_bool a -> a
    | LogicalOr, _, (_, BoolLiteral true) when is_bool a -> b

    | _ -> (location, BinaryOp (op, a, b))
    end

  | Evaluate_type -> 
    let b = evaluate_expression env frame mode b in
    begin match a, b with
    | (_, BoolLiteral _), (_, BoolLiteral _) -> a
    | _ -> raise error_type_mismatch
    end
    
  | Evaluate_const ->
    begin match op, a with
    | LogicalAnd, (_, BoolLiteral false) -> a
    | LogicalAnd, (_, BoolLiteral true) -> evaluate_expression env frame mode b
    | LogicalOr, (_, BoolLiteral false) -> evaluate_expression env frame mode b
    | LogicalOr, (_, BoolLiteral true) -> a
    | _, _ -> raise error_type_mismatch
    end

and evaluate_index env frame mode location indexable index =
  let indexable = evaluate_expression env frame mode indexable in

  match index with
  | None when is_const_type indexable -> (location, Index (indexable, None))
  | None -> raise (Error "expected an index sub-expression")
  | Some index ->
    match indexable with
    | _, DynamicArray (elements, Some element_type) ->
      let index = evaluate_expression env frame mode index in
      begin match mode, index with
      | Evaluate_type, (_, IntLiteral _) -> representative_value_of_type element_type (* must not perform a bounds check *)
      | Evaluate_const, (_, IntLiteral i)
      | Fold_consts, (_, IntLiteral i) ->
        if i < 0 || i >= Array.length elements then
          raise (error_invalid_operation (Printf.sprintf "array index out of bounds: %d" i));
        elements.(i)
      | Fold_consts, _ -> (location, Index (indexable, Some index))
      | _ -> raise error_type_mismatch
      end

    | _, Tuple elements ->
      let index = evaluate_const_value env frame index in
      begin match index with
      | _, IntLiteral i ->
        (try
          List.nth elements i
        with
        | Invalid_argument _
        | Failure _ -> raise (error_invalid_operation (Printf.sprintf "tuple index out of bounds: %d" i)))
      | _ -> raise error_type_mismatch
      end

    | _ ->
      let indexable_type = evaluate_expression env frame Evaluate_type indexable in
      begin match indexable_type with
      | _, Tuple _ -> location, Index (indexable, Some (evaluate_const_value env frame index))
      | _, DynamicArray _ -> (location, Index (indexable, Some (evaluate_expression env frame mode index)))
      | _ -> raise error_type_mismatch
      end

and evaluate_unary_op env frame mode location op e =
  let e = evaluate_expression_new env frame mode e in
  match mode, op, e with
  | _, Negate, (Const, (_, IntLiteral v)) -> Const, (location, IntLiteral (-v))
  | _, LogicalNot, (Const, (_, BoolLiteral b)) -> Const, (location, BoolLiteral (not b))
  | _, BitwiseInvert, (Const, (_, IntLiteral v)) -> Const, (location, IntLiteral (lnot v))
  | _, BitwiseInvert, (Const, (_, BoolLiteral b)) -> Const, (location, BoolLiteral (not b))
  
  | Fold_consts, Negate, (_, (_, IntLiteral _))
  | Fold_consts, BitwiseInvert, (_, (_, IntLiteral _)) ->
    Non_const (location, UnaryOp (op, ast_of e)),
              representative_value_of_type (location, Type Int)

  | Fold_consts, LogicalNot, (_, (_, BoolLiteral _))
  | Fold_consts, BitwiseInvert, (_, (_, BoolLiteral _)) ->
    Non_const (location, UnaryOp (op, ast_of e)),
              representative_value_of_type (location, Type Bool)

  | _ -> raise error_type_mismatch


and evaluate_binary_op env frame mode location op a b =
  if op = LogicalAnd || op = LogicalOr then evaluate_logical_op env frame mode location op a b else
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match op, a, b with
  | Plus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a + b))
  | Minus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a - b))
  | Times, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a * b))

  | Less, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a < b))
  | LessEquals, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a <= b))
  | Greater, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a > b))
  | GreaterEquals, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a >= b))

  | Div, (_, IntLiteral num), (_, IntLiteral denom)
  | Modulo, (_, IntLiteral num), (_, IntLiteral denom) ->
    if denom = 0 then begin
      match mode with
      | Fold_consts -> (location, BinaryOp (op, a, b)) (* TODO: new rule for CTCEs - division and modulo expressions are not CTCEs if the denominator is zero *)
      | Evaluate_type -> representative_value_of_type (location, Type Int)
      | Evaluate_const -> raise (error_invalid_operation "division by zero")
    end else
      (location, IntLiteral (if op = Div then num / denom else num mod denom))

  | ShiftLeft, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lsl b))
  | ShiftRight, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a asr b))

  | BitwiseAnd, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a land b))
  | BitwiseAnd, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a && b))
  | BitwiseOr, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lor b))
  | BitwiseOr, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a || b))
  | BitwiseXor, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lxor b))
  | BitwiseXor, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a <> b))

  | Equals, a, b
  | NotEquals, a, b ->
    if is_const_value a && is_const_value b && (const_types_equal (type_of_expression a) (type_of_expression b)) then
      let are_equal = const_values_equal a b in
      (location, BoolLiteral (if op = Equals then are_equal else not are_equal))
    else begin
      match mode with
      | Fold_consts -> (location, BinaryOp (op, a, b))
      | _ -> raise error_type_mismatch
    end

  | Plus, _, _
  | Minus, _, _
  | Times, _, _
  | Div, _, _
  | Modulo, _, _
  | Less, _, _
  | LessEquals, _, _
  | Greater, _, _
  | GreaterEquals, _, _ ->
    begin match mode with
    | Fold_consts -> (location, BinaryOp (op, a, b))
    | _ -> raise error_type_mismatch
    end

  (* TODO: the rest of them *)
  | _ -> print_endline (Printf.sprintf "binary operator not implemented: %s" (Ast.show_binary_op op)); assert false

and evaluate_conditional env frame mode location condition consequent alternative =
  let consequent_type = evaluate_expression env frame Evaluate_type consequent in
  let alternative_type = evaluate_expression env frame Evaluate_type alternative in
  if not (const_types_equal (type_of_expression consequent_type) (type_of_expression alternative_type)) then
    raise error_type_mismatch;

  let condition = evaluate_expression env frame mode condition in
  match mode with
  | Fold_consts ->
    let consequent = evaluate_expression env frame mode consequent in
    let alternative = evaluate_expression env frame mode alternative in
    begin match condition with
    | _, BoolLiteral true -> consequent
    | _, BoolLiteral false -> alternative
    | _ -> (location, Conditional (condition, consequent, alternative))
    end

  | Evaluate_type ->
    begin match condition with
    (* In Evaluate_type mode we only need a representative value of the correct type.
       Since we have already confirmed that the branches share the same type, returning the
       `alternative` branch is sufficient (and avoids needing to inspect the boolean value).
       The pattern match also ensures the condition is boolean. *)
    | _, BoolLiteral _ -> alternative (* or consequent; it doesn't matter which one we choose *)
    | _ -> raise error_type_mismatch
    end
    
  | Evaluate_const ->
    match condition with
    | _, BoolLiteral true -> evaluate_expression env frame mode consequent
    | _, BoolLiteral false -> evaluate_expression env frame mode alternative
    | _ -> raise error_type_mismatch

and evaluate_fall_through env frame mode location a b =
    (*
      Lower a match/fall-through into a purely expression-level conditional.

      The bind pass already created distinct slots for each `BoundLet` in the
      pattern and ensured that those slots are only ever referenced (via
      BoundIdentifier) in the body/guard of this match. In other words, by the
      time const-eval runs, the only way any code can observe a `BoundLet` slot is
      via the successful path of this match.

      That means we can safely evaluate the assignment unconditionally (even on
      a failing match) because no outside code can read from those slots unless
      the match succeeds. This keeps the lowering simple and avoids needing a
      special “match-failure” mechanism in this pass.

      The result of a match is then:

        if (pattern-matches && condition) then (bind; body) else next

      which is exactly what `Fall_through` / `Match` are intended to express.

      For example, this code:

        (let a, C, D) ~ v when guard in body
      | next

      becomes

        let t = v in (let a, _, _) = t in ((t[1]==C && t[2]==D && guard) ? body : next)

      where t is a temporary variable. Note that this lowering does not bring 'a'
      into lexical scope of 'next' because it happens _after_ the bind pass.
  *)
  let rec substitute_let_any expression =
    match expression with
    | _, BoundLet _ -> expression
    | location, Tuple elements -> location, Tuple (List.map substitute_let_any elements)
    | location, _ -> location, BoundLet (Any, unbindable_slot)
  in
  let rec lower_pattern_match pattern value =
    match pattern, value with
    | (location, BoundLet _), _ -> (location, BoolLiteral true)
    | (location, Tuple pattern_elements), (_, Tuple value_elements) ->
      (try
        List.fold_left2 (fun acc pattern_element value_element ->
          let element_match = lower_pattern_match pattern_element value_element in
          (location, BinaryOp (LogicalAnd, acc, element_match))
        ) (location, BoolLiteral true) pattern_elements value_elements
      with Invalid_argument _ -> raise error_type_mismatch)
    | (location, Tuple pattern_elements), _ ->
      let rec helper idx pattern_elements =
        match pattern_elements with
        | [] -> (location, BoolLiteral true)
        | (_, BoundLet _) :: rest -> helper (idx + 1) rest
        | head :: rest -> (location, BinaryOp (LogicalAnd, (location, BinaryOp (Equals, head, (location, Index (value, Some (location, IntLiteral idx))))), helper (idx + 1) rest))
      in
      helper 0 pattern_elements     
    | _ -> location, BinaryOp (Equals, pattern, value)
  in
  begin match a with
  | location, Match (pattern, value, condition, body, temp_slot) ->
    let temp_identifier = (location, BoundIdentifier ("$v", temp_slot)) in
    let lowered = location, In (
      (location, Assignment ((location, BoundLet (Identifier "$v", temp_slot)), value)),
      (location, In (
        (location, Assignment (substitute_let_any pattern, temp_identifier)),
        (location, Conditional (
          (location, BinaryOp (LogicalAnd,
            lower_pattern_match pattern temp_identifier,
            condition)),
          body,
          b)))))
    in
    (*print_endline (Printf.sprintf "lowered fall-through to: %s" (Ast.show_expression lowered));*)
    evaluate_expression env frame mode lowered
        
  | _ -> raise (Error "left hand side of a fall-through is not a pattern match expression")
  end
  

and evaluate_match env frame mode location pattern value condition body temp_slot =
  evaluate_expression env frame mode (location, Fall_through ((location, Match (pattern, value, condition, body, temp_slot)), (location, Tuple [])))

and evaluate_assignment env frame mode location a b =
  let b = evaluate_expression env frame mode b in

  let rec get_indexed_element (container : expression) (indices : int list) : expression =
    match indices with
    | [] -> container
    | i :: rest ->
      match container with
      | _, DynamicArray (elements, Some _) ->
        if i < 0 || i >= Array.length elements then
          raise (error_invalid_operation (Printf.sprintf "array index out of bounds: %d" i));
        get_indexed_element elements.(i) rest
      | _, Tuple elements ->
        (try
          let element = List.nth elements i in
          get_indexed_element element rest
        with
        | Invalid_argument _
        | Failure _ -> raise (error_invalid_operation (Printf.sprintf "tuple index out of bounds: %d" i)))
      | _ -> raise error_type_mismatch

  and set_indexed_element (container : expression) (indices : int list) (new_value : expression) : expression =
    match indices with
    | [] -> new_value
    | i :: rest ->
      match container with
      | _, DynamicArray (elements, Some element_type) ->
        if i < 0 || i >= Array.length elements then
          raise (error_invalid_operation (Printf.sprintf "array index out of bounds: %d" i));
        let updated = set_indexed_element elements.(i) rest new_value in
        let elements = Array.copy elements in
        elements.(i) <- updated;
        (location, DynamicArray (elements, Some element_type))
      | _, Tuple elements ->
        let len = List.length elements in
        if i < 0 || i >= len then
          raise (error_invalid_operation (Printf.sprintf "tuple index out of bounds: %d" i));
        let elements =
          List.mapi (fun j e -> if j = i then set_indexed_element e rest new_value else e) elements in
        (location, Tuple elements)
      | _ -> raise error_type_mismatch

  and type_after_indices (const_type : expression) (indices : int list) : expression =
    match indices with
    | [] -> const_type
    | i :: rest ->
      match const_type with
      | _, Index (element_type, None) -> type_after_indices element_type rest
      | _, Tuple elements ->
        (try
          let element = List.nth elements i in
          type_after_indices element rest
        with
        | Invalid_argument _
        | Failure _ -> raise (error_invalid_operation (Printf.sprintf "tuple index out of bounds: %d" i)))
      | _ -> raise error_type_mismatch

  and assign (indices : int list) (a : expression) (b : expression) : expression =
    match a, b with
    | (_, BoundIdentifier (display_name, slot)), _ ->
      let assignable = get_assignable frame slot in
      let value = get_assignable_value assignable in
      begin match mode, value with
      | Fold_consts, _ -> a

      | Evaluate_type, Uninitialized_of_type None -> raise (Saw_uninitialized display_name)
      | Evaluate_type, Uninitialized_of_type (Some const_type)
      | Evaluate_type, Non_const_of_type const_type ->
        representative_value_of_type (type_after_indices const_type indices)
      | Evaluate_type, Const_of_value const_value ->
        get_indexed_element const_value indices

      | Evaluate_const, Uninitialized_of_type _ -> raise (Saw_uninitialized display_name) (* Raising this leaves the local frame unreachable so any side effects so far don't matter *)
      | Evaluate_const, Non_const_of_type _ -> raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name)
      | Evaluate_const, Const_of_value current ->
        if not slot.mut then
          raise (error_immutable_assignment display_name);
        let element_type = type_of_expression (get_indexed_element current indices) in
        let b = implicit_convert mode b element_type in
        let updated = set_indexed_element current indices b in
        set_assignable_value assignable (check_is_const_value updated);
        b (* The result should be the RHS, implicitly converted to the same type as the LHS *)
      end

    | (_, BoundLet (pattern, slot)), _ ->
      if is_slot_bindable slot then begin
        let assignable = get_assignable frame slot in
        if mode = Fold_consts then begin
          if is_const_value b then begin
            let b = match pattern with
            | Identifier name -> set_lambda_aliases b (location, BoundIdentifier (name, slot))
            | _ -> set_lambda_aliases b (location, BoundIdentifier ("_", slot)) in
            set_assignable_value assignable (check_is_const_value b)
          end else begin
            set_assignable_value assignable (Non_const_of_type (type_of_expression (evaluate_expression env frame Evaluate_type b)))
          end
        end else begin
          (* This goes quite a bit differently than for BoundIdentifier. The main reason is because the assignment of a BoundLet _is_ it's initialization,
            whereas, BoundIdentifiers are always initialized before any reassignment. *)
          set_assignable_value assignable (check_is_const_value b);
        end
      end;
      if mode = Fold_consts then
        location, BoundLet (pattern, slot)
      else
        (* The result should be the RHS, implicitly converted to the same type as the LHS, but the type of the LHS is inferred from the RHS in this case *)
        b

    | (_, Index (indexable, Some index)), _ ->
      let index = match evaluate_expression env frame Evaluate_type indexable with
        | _, Tuple _ -> evaluate_const_value env frame index
        | _, DynamicArray _ -> evaluate_expression env frame mode index
        | _ -> raise error_type_mismatch in
      if mode = Fold_consts then
        location, Index (assign [] indexable b, Some index)
      else begin
        let index = match index with
          | _, IntLiteral i -> i
          | _ -> raise error_type_mismatch in
        assign (index::indices) indexable b
      end
    | (_, Tuple froms), (_, Tuple tos) ->
      (try
        (location, Tuple (List.map2 (assign [])  froms tos))
      with Invalid_argument _ -> raise error_type_mismatch)

    | (_, Tuple froms), _ ->
      if mode = Fold_consts then
        location, Tuple (List.mapi (fun i from_element -> assign [] from_element (location, Index (b, Some (location, IntLiteral i)))) froms)
      else
        raise error_type_mismatch

    | _ -> raise (error_internal (Printf.sprintf "assignment target not implemented: %s" (Ast.show_expression a))) in

  if mode = Fold_consts then
    (location, Assignment ((assign [] a b), b))
  else
    assign [] a b

and evaluate_in env frame mode location a b =
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match mode with
  | Fold_consts -> (location, In (a, b))
  | Evaluate_type
  | Evaluate_const -> b

and evaluate_call env frame mode location callee args call_modifiers =
  if mode = Evaluate_const then increment_loop_count ();
  (* Consistent with other imperative languages, semantically, the callee is evaluated before any arguments. *)
  let callee = evaluate_expression env frame mode callee in
  let args = List.map (evaluate_expression env frame mode) args in
  let call_modifiers = { call_modifiers with pure = call_modifiers.pure || call_modifiers.const } in
  match mode, callee with
  | Fold_consts, (_, Lambda (_, _, lambda_modifiers, _,_)) ->
    if call_modifiers.const then begin
      if not lambda_modifiers.const then
        raise (Error "cannot call non-const lambda at compile time");
      let args = List.map (evaluate_const_value env frame) args in
      evaluate_const_value env frame (location, Call (callee, args, call_modifiers))
    end else
      (location, Call (callee, args, call_modifiers))

  | Evaluate_type, (_, Lambda (return_type, _, _, _, _)) ->
    representative_value_of_type return_type

  | Evaluate_const, (_, Lambda (return_type, params, lambda_modifiers, (_, BoundFrame (num_variables, statement)), Some (_, Closure (closure_frame, _)))) ->
    if not lambda_modifiers.const then
      raise (error_invalid_operation "cannot call non-const lambda in a constant expression");
    let callee_frame = {
      depth = closure_frame.depth+1;
      enclosing_frame = Some closure_frame;
      variables = Array.make num_variables empty_variable;
      return_type = return_type;
      pure = true;
      const = true;
    } in
    List.iteri (fun i (location, param) -> match param with
      | BoundDeclaration ({type_expr=Some type_expr; _}, slot) ->
        let arg = List.nth args i in
        let arg = implicit_convert mode arg type_expr in
        set_assignable_value (get_assignable callee_frame slot) (check_is_const_value arg)
      | _ -> raise (error_internal (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))))) params;
    (try
      evaluate_statement env callee_frame mode statement |> ignore;
      match return_type with
      | _, Tuple [] -> (location, Tuple [])
      | _ -> raise (Error "missing return statement")
    with
    | Return_exn return_value ->
      if not (is_const_value return_value) then
        raise (error_internal "non-constant return value should be impossible");
      return_value)

  | _, (_, Lambda _) -> raise (error_internal (Printf.sprintf "all lambdas should have closures added before calling them: %s" (Ast.show_expression callee)))

  | _ -> (location, Call (callee, args, call_modifiers))

and evaluate_tuple env frame mode location elements =
  (location, Tuple (List.map (evaluate_expression env frame mode) elements))
  
and evaluate_dynamic_array_literal env frame mode location elements element_type : expression =
  if Array.length elements = 0 then begin
    match element_type with
    | Some _ -> (location, DynamicArray (elements, element_type))
    | _ ->
      (* TODO: we plan to allow empty array literals in some special cases where the element type is known, including initializers, the RHS of some assignments and function call arguments *)
      raise (Error "cannot infer type of empty array literal")
  end else begin
    let elements = Array.map (evaluate_expression env frame mode) elements in

    (* Fold_consts is responsible for checking all the elements are the same type iff
      it is necessary to do so the for constant folding, i.e. if the resulting array literal will be
      considered a constant value. *)
    if mode <> Fold_consts || Array.for_all is_const_value elements then begin
      let element_type = match element_type with
      | Some element_type -> element_type
      | _ -> type_of_expression elements.(0) in
      if Array.exists (fun e -> not (const_types_equal (type_of_expression e) element_type)) elements then
        raise error_type_mismatch;
      (location, DynamicArray (elements, Some element_type))
    end else
      (location, DynamicArray (elements, element_type))
  end

and evaluate_arity env frame mode location e =
  match mode with
  | Fold_consts ->
    let e = evaluate_expression env frame mode e in
    begin match evaluate_expression env frame mode e with
    | _, Tuple elements -> (location, IntLiteral (List.length elements))
    | _ when is_const_value e -> (location, IntLiteral 1)
    | _ -> (location, Arity e)
    end

  | Evaluate_type -> representative_value_of_type (location, Type Int)
  | Evaluate_const ->
    let e = evaluate_expression env frame mode e in
    match e with
    | _, Tuple elements -> (location, IntLiteral (List.length elements))
    | _ -> (location, IntLiteral 1)

and evaluate_lambda_part1 _ frame mode location return_type params modifiers body_location num_variables statement =
  match mode with
  | Evaluate_type ->
    representative_value_of_type (type_of_expression (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), None)))
  | _ ->
    let modifiers = { modifiers with pure = modifiers.pure || modifiers.const } in
    if frame.const && not modifiers.const then
      raise error_expected_const_lambda;
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (distinct_closure_identity (), Closure (frame, None))))

and evaluate_lambda_part2 env mode part1 =
  match mode, part1 with
  | Evaluate_type, _ ->
    part1
  | _, (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (closure_identity, Closure (frame, _)))) ->
    let lambda_frame = {
      depth = frame.depth + 1;
      enclosing_frame = Some frame;
      variables = Array.make num_variables empty_variable;
      return_type = return_type;
      pure = modifiers.pure;
      const = modifiers.const
    } in
    let return_type = check_is_const_type (evaluate_const_value env frame return_type) in
    let params = List.map (fun (location, param) -> match param with
      | BoundDeclaration ({init_expr=init_expr; type_expr=Some type_expr; name=name; modifiers=modifiers}, slot) ->
        let type_expr = check_is_const_type (evaluate_const_value env frame type_expr) in
        set_assignable_value (get_assignable lambda_frame slot) (Non_const_of_type type_expr);
        (location, BoundDeclaration ( { init_expr=init_expr; type_expr = Some type_expr; name=name; modifiers=modifiers }, slot))
      | _ -> raise (error_internal (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))))) params in
    let statement = evaluate_statement env lambda_frame Fold_consts statement in
    (* A subsequent pass will verify that the lambda meets the requirements for pure or const. *)
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (closure_identity, Closure (frame, None))))
  | _ -> assert false

and evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statement _ =
  let part1 = evaluate_lambda_part1 env frame mode location return_type params modifiers body_location num_variables statement in
  evaluate_lambda_part2 env mode part1

and evaluate_typeof env frame _ _ e =
  type_of_expression (evaluate_expression env frame Evaluate_type e)

and evaluate_expression_statement env frame mode location statement =
  match mode with
  | Fold_consts -> (location, Statement (evaluate_statement env frame mode statement))
  | Evaluate_const -> evaluate_statement env frame mode statement |> ignore; (location, Tuple [])
  | Evaluate_type -> assert false

and set_lambda_aliases (location, const_value) ast_alias =
  let ith_index i e = set_lambda_aliases e (location, Index (ast_alias, Some (location, (IntLiteral i)))) in
  match const_value with
  | Lambda (return_type, params, modifiers, statement, Some (closure_identity, Closure (frame, _))) ->
    (location, Lambda (return_type, params, modifiers, statement, Some (closure_identity, Closure (frame, Some ast_alias))))
  | Tuple elements -> (location, Tuple (List.mapi ith_index elements))
  | DynamicArray (elements, element_type) -> (location, DynamicArray ((Array.mapi ith_index elements), element_type))
  | _ -> (location, const_value)

and evaluate_declaration env frame mode location declaration slot =
  assert (mode <> Evaluate_type);

  let assignable = get_assignable frame slot in

  let initialize_assignable type_expr init_expr =
    if (declaration.modifiers.mut || not (is_const_value init_expr)) then begin
      if mode=Evaluate_const && frame.const then
        let init_expr = set_lambda_aliases init_expr (location, BoundIdentifier (declaration.name, slot)) in
        set_assignable_value assignable (check_is_const_value init_expr)
      else        
        set_assignable_value assignable (Non_const_of_type type_expr)
    end else
      let init_expr = set_lambda_aliases init_expr (location, BoundIdentifier (declaration.name, slot)) in
      set_assignable_value assignable (check_is_const_value init_expr) in
      
  match declaration with
  | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
    let type_expr = check_is_const_type (evaluate_const_value env frame type_expr) in
    set_assignable_value assignable (Uninitialized_of_type (Some type_expr));
    let init_expr = implicit_convert mode (evaluate_expression env frame mode init_expr) type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot)

  | { type_expr=Some type_expr; init_expr=None; _} ->
    let type_expr = check_is_const_type (evaluate_const_value env frame type_expr) in
    let init_expr = default_value type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot)

  (* This form of declaration is only used for lambda expressions. *)
  | { type_expr=None; init_expr=Some (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), _)) ; _} ->
    let init_expr = match get_assignable_value assignable with
    | Const_of_value part1 -> part1 (* If a previous attempt at part 2 aborted, skip part 1, ensuring that closure identity is preserved. *)
    | _ ->
      evaluate_lambda_part1 env frame mode location return_type params modifiers body_location num_variables statement in
    (initialize_assignable (type_of_expression init_expr) init_expr;
    let init_expr = evaluate_lambda_part2 env mode init_expr in
    let type_expr = check_is_const_type (type_of_expression init_expr) in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot))
    
  | _ -> print_endline (Printf.sprintf "declaration not implemented: %s" (Ast.show_declaration declaration)); assert false

and evaluate_if env frame mode location condition consequent alternative =
  let condition = evaluate_expression env frame mode condition in
  match mode with
  | Fold_consts ->
    let consequent = evaluate_statement env frame mode consequent in
    let alternative = evaluate_statement env frame mode alternative in
    (location, If (condition, consequent, alternative))

  | Evaluate_const ->
    begin match condition with
    | _, BoolLiteral true -> evaluate_statement env frame mode consequent
    | _, BoolLiteral false -> evaluate_statement env frame mode alternative
    | _ -> raise error_type_mismatch
    end

  | Evaluate_type -> assert false

and evaluate_do_while env frame mode location body condition =
  match mode with
  | Fold_consts ->
    let body = evaluate_statement env frame mode body in
    let condition = evaluate_expression env frame mode condition in
    (location, DoWhile (body, condition))

  | Evaluate_const ->
    let rec loop () =
      increment_loop_count ();
      evaluate_statement env frame mode body |> ignore;
      match evaluate_expression env frame mode condition with
      | _, BoolLiteral true -> loop ()
      | _, BoolLiteral false -> ()
      | _ -> raise error_type_mismatch in
    loop ();
    (location, DoWhile (body, condition))

  | Evaluate_type -> assert false

and evaluate_return env frame mode _ e =
  let e = implicit_convert mode (evaluate_expression env frame mode e) frame.return_type in
  match mode with
    | Fold_consts -> e
    | Evaluate_type -> assert false
    | Evaluate_const -> raise (Return_exn e)


and implicit_convert mode from_expression to_type =
  match mode with
  | Fold_consts -> from_expression (* just leave the node in place for a subsequent pass to actually do the implicit conversion *)
  | Evaluate_type -> assert false; (* never actually called in this mode *)
    (*representative_value_of_type (to_type_location, to_type)*) (* leave it to a subsequent pass to determine whether the conversion is valid *)
  | Evaluate_const ->
    let from_type = type_of_expression from_expression in
    match to_type with
    | _, Type Type when is_const_type from_expression -> from_expression
    | _ when const_types_equal from_type to_type -> from_expression
    | _ -> raise error_type_mismatch

let const_evaluate_program (env : env) (frame : frame) (statement : statement) : statement =
  evaluate_statement env frame Fold_consts statement
