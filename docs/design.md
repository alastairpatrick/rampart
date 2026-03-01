Design: Static Type Checking and Compile-Time Constants
======================================================

Purpose and goals
-----------------
This document records the short-term design for adding static type checking to Rampart by restricting declaration type expressions to a well-defined class of compile-time constants. The goal is to make type expressions fully evaluable at compile time so we can (1) build a static type environment, (2) run a sound static type checker, and (3) lower the program into a statically-typed IR amenable to ahead-of-time optimizations.

Design constraints and assumptions
 - The implementation contains runtime scheduling and effect machinery used by the interpreter; this is an implementation detail. The const-eval pass will be independent and must treat any runtime effect as a failure condition for compile-time evaluation.

Compiler passes (up to static type checking)
--------------------------------------------
We describe the passes to implement (inputs/outputs, responsibilities):

1. Lexer
   - Input: source text
   - Output: token stream
   - Responsibility: recognize keywords (`lambda`, `pure`, `mut`, `type`, etc.), identifiers, literals, punctuation. No change required beyond existing lexer; `pure` must remain a reserved token for grammar.

2. Parser
   - Input: token stream
   - Output: raw AST (including expressions for type positions)
   - Responsibility: build AST nodes for expressions, declarations, lambdas, etc. The parser will still permit the syntactic forms allowed today (subject to grammar changes such as `pure` position). Parsing is not performing semantic checks.

3. Binder (name resolution)
   - Input: AST
   - Output: Bound AST (identifiers replaced with `BoundIdentifier`, `BoundLet`, `BoundDeclaration`, `BoundFrame` for lambdas), slot allocation metadata
   - Responsibility:
     - Determine lexical scopes and allocate slots.
     - Produce bound lambdas that capture an `enclosing_frame` depth (already implemented).
     - This pass must also record, for each bound identifier used in a declaration-type expression, the declaration slot and whether the identifier is declared `mut` or immutable. This information will be used by the compile-time-constant evaluator.

4. Compile-time constant evaluator (const-eval)
   - Input: bound AST and the binding environment (slot metadata)
   - Output: a mapping from declaration -> compile-time-evaluated value (for declarations whose `type_expr` qualifies), or explicit compile-time error rejecting non-constant `type_expr`s
   - Responsibilities and rules (see next section for the formal rules):
     - Decide whether an expression is a compile-time constant following the conservative rules below.
     - Evaluate constant expressions deterministically and without performing runtime effects (no I/O, no access to mutable captured variables).
     - Mark declaration `type_expr` as resolved to a runtime `typ` (the internal type representation) if it is compile-time-constant and of category `type`; otherwise produce a compile-time error.
   - Implementation notes:
    - The evaluator must be conservative. If evaluation would access a mutable captured slot, the const-eval should abort and report the expression as non-constant.
    - Calls are allowed only when the callee is provably pure and total, and all argument expressions are compile-time constants.
    - The const-eval must be implemented as a focused, deterministic evaluator separate from the interpreter. It should abort on encountering any runtime-only behavior.

5. Static type checker
   - Input: bound AST + resolved declaration types (from const-eval)
   - Output: type-annotated AST or typed IR; list of type errors
   - Responsibilities:
     - Use the compile-time-resolved types to build the global type environment.
     - Type-check function bodies, expressions, and declarations using the resolved static types.
     - Reject programs where inferred/declared types mismatch, or where runtime-only type constructs are used in type positions.
   - Implementation notes:
     - The checker should operate in phases: (a) collect resolved declaration types, (b) check signatures (function arities, parameter types), (c) check bodies (ensuring return types match, variables are used according to their types), (d) check purity constraints where relevant.
     - For now the checker can be strict and require explicit type annotations on declarations; later we may add type inference.

Rules for compile-time constants
--------------------------------
A compile-time constant expression (CTCE) is an expression that can be evaluated deterministically at compile time without causing runtime effects or depending on mutable state. Conservative rules:

1. Base cases (immediate constants)
   - type literals: `int`, `bool`, `type`, `void` are constants.
   - integer/boolean literals (e.g., `7`, `true`). For clarity: numeric literals can be used in type-level tuples for convenience (e.g., `(int, 7)`) but this should be limited to contexts where they make sense.

2. Identifiers
   - An identifier `x` is a CTCE only if:
     - `x` is bound to a declaration that is immutable (`mut = false`), and
     - the declaration's initializer (or the RHS of a `let` that defines it) itself is a compile-time constant.
   - Note: this requires the binder to indicate whether the referenced declaration is `mut` and to provide the initializer expression for const-eval.

3. Composed expressions
   - A composition (e.g., tuple construction, binary operations like `1+1`, construction of function types `int(int, bool)`) is a CTCE if all operand subexpressions are CTCEs and the syntactic operation is semantically constant (no allocation or side-effects that would change observable state).

4. Function calls
   - A call `f(a1, a2, ...)` is a CTCE only if:
     - `f` is a known function value that is provably pure and total (e.g. no mutation of captured state), and
     - every argument `ai` is a CTCE, and
     - `f`'s behavior on constant inputs is deterministic and guaranteed not to depend on run-time environment or global mutable state.
   - Practically, make this conservative: allow only calls to functions marked/annotated as `const` or `pure` where purity is statically known.

5. Forbidden constructs
   - Any expression that may cause I/O or access mutable captured slots is not a CTCE.

Where CTCEs must be used
-----------------------
- Declaration `type_expr`: every `declaration.type_expr` that will be used for static type checking must be a CTCE and must evaluate to an entity of kind `type`. If not, compilation fails with a clear message.
- Potential extensions: other compile-time computed metadata (e.g., size/layout annotations, compile-time macros) may also require CTCEs.

Practical notes for implementation
----------------------------------
- Use the binder output to supply the const-eval with a directed acyclic graph of initializer dependencies to avoid infinite recursion; detect cycles and report errors.
-- Evaluate const expressions in a small-step deterministic evaluator distinct from runtime evaluation. This evaluator should:
  - Treat any attempt to perform runtime scheduling, blocking, or other effects as an immediate failure (raise an error) rather than trying to emulate the runtime.
  - Reject attempts to read `Uninitialized` slots or mutable captured slots.
  - Allow only allowed builtins and pure/annotated functions.
- Purity and totality for called functions:
  - Start with a conservative annotation-based approach: only functions annotated `pure` and optionally `const` are allowed in compile-time calls.
  - Later, you can add static purity analysis; dynamic checks are not sufficient for compile-time evaluation.

Errors and diagnostics
----------------------
- If a declaration `type_expr` is not a CTCE or does not evaluate to a type, emit a clear compile-time error referencing the declaration site.
-- If const-eval encounters a runtime scheduling/blocking action or a mutable access, report that the expression is not a compile-time constant and indicate why.

Benefits and limitations
------------------------
- Benefits:
  - Once declaration types are compile-time constants, you can build a fixed type environment and perform full static checking.
  - Static types make further optimizations possible: monomorphization, efficient calling conventions, removal of runtime type tags, and more predictable memory layout.
- Limitations & further work:
  - To approach performance parity with Java/C#/Rust you will need further work: AOT code generation, an optimizing backend, monomorphization for parametric code, and a managed runtime design (or native codegen).
  - Generic/polymorphic features complicate const-eval and static checking; design decisions will be required.

Next practical steps (implementation plan)
-----------------------------------------
1. Add a `const_eval` module (or pass) that consumes bound AST and outputs resolved declaration types or errors.
2. Modify `bind.ml` to record initializer expressions and immutability for identifiers used in type positions.
3. Implement the static type checker pass that relies on resolved declaration types from `const_eval`.
4. Add test coverage: positive/negative tests for CTCEs (including pure-call const-eval), and end-to-end tests that verify static type errors are reported at compile time.

Appendix: Example
-----------------
- Valid declaration-type expressions:
  - `int`, `bool`
  - `let x = int;` then `x` (if `x` is immutable and initializer is constant)
  - `int(int, bool)` where `int` and `bool` are constants
  - `CONST_FN(int)` where `CONST_FN` is a marked pure/const function and `int` is a constant

-- Invalid declaration-type expressions (rejected by const-eval):
  - `let x = some_runtime_call();` then `x` used as a type
  - any expression that would cause runtime scheduling/blocking or that depends on `mut` captured state



