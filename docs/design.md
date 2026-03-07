**Rampart Design (Updated)**

This document describes the current design of Rampart's compile-time constant
evaluation (CTCE), `pure` / `const` function semantics, and the compiler passes
that lead up to static type checking. It's intentionally pragmatic — CTCE is
conservative, avoids emulating runtime scheduling, and favors diagnostics that
help later passes finish work safely.

**Goals**
- Allow some expressions (types, initializer expressions) to be resolved at
  compile time so the static type checker can depend on those values.
- Ensure compile-time evaluation is deterministic and side-effect free.
- Provide clear, testable diagnostics when CTCE cannot proceed.

**Key Concepts**
- Frame: a small runtime-like environment used by const-eval to model locals
  and captured variables. Frames are kept alive by
  a garbage collector if referenced by closures; however CTCE must still enforce
  semantic restrictions to preserve determinism.
- CTCE (const-eval): a conservative evaluator that substitutes compile-time
  constant values into AST nodes so later passes can operate on concrete
  expressions.
- `pure` functions: runtime restriction enforced elsewhere (caller/callee
  rules) preventing side-effectful operations in pure contexts.
- `const` lambdas: stronger than `pure`. A `const` lambda can be executed at
  compile time but only if all captured variables it reads are known CTCEs and
  the returned values are themselves CTCEs.

**Passes and Modes**
- Lex / Parse / Bind: standard front-end phases produce a `Bound` AST where
  identifiers are replaced with `BoundIdentifier` (with `slot` info) and
  lambdas are bound into frames. Lambdas carry an optional closure field (a
  `Closure frame`) which the const-eval pass will populate for `const`
  functions.
- Const-eval pass runs in three related modes:
  - `Search_for_declaration_types` — the default traversal used when the
    front end first visits a program. It walks the AST looking for
    declarations whose *types* need to be resolved and, when a declaration is
    encountered, immediately evaluates its type by recursively invoking
    `Evaluate_const` on the type expression.  For other expressions the
    traversal remains conservative: identifiers are left untouched and calls
    are not evaluated outside of a declaration type.  This strategy prevents
    spurious cyclic-dependency errors and avoids accidental side effects while
    still ensuring that the _types_ of declarations are normalized early.

    Regardless of the mode, the pass has no obligation to expose or explain
    the contents of a `Closure` frame to any later phase.  The only values that
    escape const-eval are fully resolved types (or lambda expressions typed as
    call‑types), and the invariant is that a subsequent pass will never need
    to look inside a closure in order to compute a type.  Consequently there is
    a clean *firewall* between const-eval and its successors: downstream
    passes (e.g. static type checking) can treat closure annotations as
    opaque metadata or even ignore them entirely.  The type system itself is
    oblivious to the runtime environment captured by a const lambda, so there
    is no semantic dependency on the const-eval representation.

  - `Evaluate_type` — a lightweight helper mode used when the pass needs the
    *type* of an arbitrary expression without performing any side-effects or
    unrolling of const lambdas.  It returns a representative value for the
    expression's type.  (This mode isn’t used on statements.)
  - `Evaluate_const` — full CTCE mode for evaluating a specific expression
    (typically a declaration type). This mode may substitute identifier values
    and execute `const` lambdas, but only under strict checks (the lambda's
    modifiers.const flag must be true, and it must carry a closure frame when
    it is executed), arguments are required to be previously identified as
    CTCEs or otherwise accepted, return values are checked for const-ness via
    `is_const_value`, etc.).  As noted above, `Search_for_declaration_types`
    dispatches to `Evaluate_const` when evaluating a declaration's type.  By
    contrast, declaration *initializers* are evaluated only in whichever mode
    the pass was invoked with (usually `Search_for_declaration_types`), and
    the pass itself does not write initializer expressions back into the
    program; only evaluated declaration *types* are committed.  Lambda
    expressions and their optional closure field are likewise not leaked out of
    CTCE except when they form part of a declaration type.

**CTCE Rules (Conservative Summary)**
- Constant forms (always CTCE): integer/boolean literals, `Type` nodes,
  tuples of CTCEs, and **any** lambda expression.  The evaluator treats
  every lambda literal as a constant value (even impure or non-`const` lambdas),
  although only `const` lambdas may be invoked in `Evaluate_const` mode.  This
  change ensures that *representative values* — the canonical elements used by
  `Evaluate_type` when synthesising a type — are themselves always constant
  values.
- Identifier substitution: allowed only in `Evaluate_const` mode and only if
  the identifier maps to `Const_of_value` (a previously-identified CTCE) or to
  `Non_const_of_value` that is *local* to a `const` frame being executed.
  Reads of mutable or non-const captured variables are rejected during
  `Evaluate_const`.

- **Representative-value invariant:** every value returned by the
  `representative_value_of_type` helper is guaranteed to satisfy
  `is_const_value`.  Because all lambdas are considered CTCE values, the
  helper never needs to return a non-constant value, and clients can safely
  treat representative values as compile-time constants when reasoning about
  types.
  (The implementation additionally permits a `Non_const_of_type` binding in the
  local const frame to be accessed, returning the identifier itself; this
  provides a representative value for type inference without forcing an actual
  constant.)
- Function calls at compile time: only `const` lambdas that carry a
  `Closure` frame (populated during evaluation of their definition) are
  eligible for execution by `Evaluate_const`.  When the call is performed the
  evaluator deliberately constructs the callee frame with both
  `pure=true` and `const=true` – ensuring that the body is treated as a
  compile-time pure/const procedure even if its source syntax omitted the
  `pure` modifier.  Argument CTCEs are bound into parameters. The body is
  executed in `Evaluate_const` mode; returns are captured via an exception
  (`Return_exn`) and validated.
  - Return values from `Evaluate_const` calls must be constant values (the
    check is performed by `is_const_value`).  The evaluator does **not** run a
    separate traversal to validate the return expression; instead any illegal
    references (for example, to slots in the callee's own frame or to mutable
    captured variables) are detected via the normal identifier lookup rules
    during evaluation, which will raise an appropriate `Located_error` if
    such a value is constructed.  This distinction is reflected in the
    implementation: `evaluate_call` simply tests `is_const_value` on the
    result and trusts earlier checks to have prevented escaping bindings.
- Assignments during `Evaluate_const`: supported only in restricted cases.
  The evaluator may update `Non_const_of_value` bindings in the current
  const-local frame, but assignments to captured mutable variables are rejected.
  (In addition, when a `Return` statement is executed the returned expression
  is implicitly converted to the enclosing function's return type; any
  mismatch produces a `type mismatch` error during const-evaluation.)
  Furthermore, if a const lambda is executed and its declared return type is
  not `void` the body must actually contain a `Return` statement; falling off
  the end of the function triggers an explicit "missing return statement"
  error during const-evaluation.  This guards against subtle issues caused by
  the implicit `()`→`Type` conversion and mirrors the requirement that later
  static checks will enforce.

**Error Handling & Diagnostics**
- CTCE raises `Located_error` for user-facing issues (cycles that prevent
  evaluating a declaration type, illegal access of mutable captured
  variables, escaping closures, etc.).
- Non-recoverable internal invariants use `error_internal` to help debug the
  compiler itself; these are not intended to be surfaced to end users.
- Unit tests use `ppx_expect` and check both successful normalized ASTs and
  diagnostic output when evaluation cannot proceed.

**Semantics Notes & Rationale**
- Big-step vs small-step: the current implementation uses a big-step
  evaluator for simplicity. If the pass later needs to reason about fine
  interleavings or step-limited evaluation to avoid halting, a small-step
  engine can be introduced.

**Testing & Coverage**
- Tests should cover:
  - Literal and tuple folding.
  - Type defaulting for declarations without initializers.
  - `Search_for_declaration_types` traversal and the fact that declaration
    *types* are eagerly evaluated (including const-calls) while other
    expressions remain inert.
  - `Evaluate_const` call execution for `const` lambdas and validation of
    returned values (reject non-CTCE).
  - Cycle detection that prevents declaration type evaluation (and expects
    `Located_error`). Non-blocking cycles that do not prevent type evaluation
    should be left for later passes (and tests should reflect that).

**Future Work / Enhancements**
- Add a small-step execution mode or an evaluation-step limit to avoid
  compile-time halting. A simple max-depth guard can be added as an
  interim safeguard.
 - Strengthen `is_const_value` to inspect the closure field and ensure
  captured variables are CTCEs where applicable.

**References**
- `lib/const_eval.ml` — current CTCE implementation.
- `lib/test_const_eval.ml` — tests driving CTCE behavior.
- `lib/evaluate.ml.legacy` — runtime evaluator; purity checks at runtime are
  complementary to CTCE checks. This file is considered legacy, though is
  still a useful reference. It will be deleted once all the features are
  implemented in the const-eval and static type checking passes.

---

Keep this document up to date as the CTCE pass expands. The design favors
correctness and conservative safety over aggressive optimization of what can
be evaluated at compile time.

