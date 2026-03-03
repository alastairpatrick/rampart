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
  and captured variables. Frames are plain OCaml records and are kept alive by
  OCaml's GC if referenced by closures; however CTCE must still enforce
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
  lambdas are bound into frames. The binder may annotate lambda nodes with
  pass-specific annotations (e.g., `Annotated (Closure frame, ...)`) to record
  capture frames.
- Const-eval pass runs in two modes:
  - `Search_for_declaration_types` — conservative traversal used to find
    declarations whose *types* must be evaluated. It performs only low-risk
    normalization (literal folding, tuple construction, type defaults) but
    does NOT substitute identifiers or evaluate function calls. This avoids
    false cyclic dependencies and prevents accidental compile-time side
    effects or halts.
  - `Evaluate_consts` — full CTCE mode for evaluating a specific declaration
    type. This mode can substitute identifier values and may execute
    `const` lambdas, but only under strict checks (callee annotated as
    `const`, arguments must be CTCEs or explicitly allowed forms, returned
    values must themselves be CTCEs, etc.). In the current design
    `Evaluate_consts` is used to evaluate *declaration types*; declaration
    initializers are evaluated only in the mode the pass was invoked with
    (typically the conservative `Search_for_declaration_types`) and are not
    automatically committed by `Evaluate_consts`. Only declaration *types*
    may escape the const-eval pass — lambda expressions and their closures
    are not written back into top-level AST nodes by CTCE.

**CTCE Rules (Conservative Summary)**
- Constant forms (always CTCE): integer/boolean literals, `Type` nodes, tuples
  of CTCEs.
- Identifier substitution: allowed only in `Evaluate_consts` mode and only if
  the identifier maps to `Const_of_value` (a previously-identified CTCE) or to
  `Non_const_of_value` that is *local* to a `const` frame being executed.
  Reads of mutable or non-const captured variables are rejected during
  `Evaluate_consts`.
- Function calls at compile time: only `const` lambdas annotated with their
  closure frame are eligible for execution by
  `Evaluate_consts`. The evaluator creates a fresh callee frame with
  `pure=true,const=true` and binds argument CTCEs into parameters. The body is
  executed in `Evaluate_consts` mode; returns are captured via an exception
  (`Return_exn`) and validated.
- Return values from `Evaluate_consts` calls must be CTCEs (pass
 - Return values from `Evaluate_consts` calls must be CTCEs (pass
  `is_const_expression`). In practice the evaluator performs a conservative
  traversal of the returned expression and rejects any *references* into the
  callee's local frame or to non-CTCE captured variables. Concretely this
  means rejecting `BoundIdentifier` nodes that resolve to slots in the callee
  frame (or deeper) and rejecting `Annotated (Closure frame, ...)` where the
  `closure` frame is the callee frame or an inner frame; such values would
  otherwise expose ephemeral mutable state to later passes.
- Assignments during `Evaluate_consts`: supported only in restricted cases.
  The evaluator may update `Non_const_of_value` bindings in the current
  const-local frame, but assignments to captured mutable variables are rejected.

**Error Handling & Diagnostics**
- CTCE raises `Located_error` for user-facing issues (cycles that prevent
  evaluating a declaration type, invalid const-calls, illegal access of
  mutable captured variables, escaping closures, etc.).
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
  - `Search_for_declaration_types` conservative behavior — do not substitute
    identifiers or evaluate calls.
  - `Evaluate_consts` call execution for `const` lambdas and validation of
    returned values (reject non-CTCE).
  - Cycle detection that prevents declaration type evaluation (and expects
    `Located_error`). Non-blocking cycles that do not prevent type evaluation
    should be left for later passes (and tests should reflect that).

**Future Work / Enhancements**
- Add a small-step execution mode or an evaluation-step limit to avoid
  compile-time halting. A simple max-depth guard can be added as an
  interim safeguard.
- Strengthen `is_const_expression` to inspect closure annotations and ensure
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

