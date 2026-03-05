# Rampart — Copilot instructions

Short, actionable notes to help AI agents contribute to Rampart (OCaml/Dune).

- **Big picture:** Rampart is an OCaml library + small executable built with Dune. The parser is written with Menhir (`lib/parser.mly`) and the lexer with ocamllex (`lib/lexer.mll`). The runtime/evaluator lives in `lib/evaluate.ml` and implements a small scheduler using OCaml effects (`Effect.Deep`) with custom `Fork` and `Defer` effects.

- **Build & test (common commands):**
  - Build: `dune build`
  - Run tests: `dune runtest`
  - Run the executable: `dune exec -- rampart` (public executable defined in [bin/dune](bin/dune))
  - Generate opam (handled by Dune): `dune build -p rampart` / see `dune-project` and `rampart.opam` for packaging details.

- **Key files to read before edits:**
  - [dune-project](dune-project) — project metadata and tool versions (Menhir).
  - [lib/dune](lib/dune) — build rules: menhir, ocamllex, ppx, inline_tests.
  - [lib/evaluate.ml](lib/evaluate.ml) — central evaluator and scheduler (effects: `Fork`, `Defer`).
  - [lib/parser.mly](lib/parser.mly) and [lib/lexer.mll](lib/lexer.mll) — grammar and lexer.
  - [bin/dune](bin/dune) and `bin/main.ml` — sample executable entry point.

- **Project-specific conventions & gotchas:**
  - Many files are preprocessed; you'll see `.pp.ml` variants generated. Do not edit generated `.pp.ml` files; edit the source (`.ml`, `.mly`, `.mll`) and run `dune build`.
  - Inline tests and expectations are enabled (`ppx_inline_test`, `ppx_expect`). Use `dune runtest` to execute them.
  - The evaluator uses a two-mode evaluation (`EvalFull` and `EvalTypeOnly`) to avoid unwanted side effects when only the type is needed — see `strip_assignability` in [lib/evaluate.ml](lib/evaluate.ml). Changes to evaluation or slot semantics must preserve the `Defer`/`representative_value_for_type` behaviour.
  - Concurrency/continuation behavior is implemented with OCaml effects (not threads). `evaluate_to_completion` maintains task and stalled queues; altering effect handling requires careful reasoning about continuations and dependency queues.

- **When editing grammar/lexer:**
  - Edit `lib/parser.mly` / `lib/lexer.mll` and run `dune build` to regenerate parser artifacts. Menhir flags are defined in [lib/dune](lib/dune).

- **Testing & debugging tips:**
  - Use `dune build` then `dune exec -- rampart` to exercise the runtime.
  - Inspect generated artifacts under `_build/default` to debug preprocessing or parser output (e.g., `_build/default/lib/parser.pp.ml`).
  - Runtime errors raise `Located_error` with location info — check `lib/diagnostic.ml`/`lib/error.ml` for error formatting.

- **Dependencies & tools:**
  - Requires Dune >= 3.20 (see `dune-project`). Menhir and ocamllex are used; ensure Menhir is available when editing grammar.

- **Code‑review checklist (project‑specific):**
  - Ensure `dune build`/`dune runtest` succeed; many edits show up only as expectation mismatches.
  - When modifying `const_eval.ml` or the evaluator, verify that `const_types_equal` and related helpers stay in sync.
  - Look for accidental uses of polymorphic `=` comparing `expression` values; prefer `const_types_equal` for types.
  - If you change the AST (e.g. lambda syntax, return shape, `BoundLet`), update parser/linker/binder and adjust all expectation strings in tests.
  - Grammar edits: avoid clashes with the established call/tuple rules; the existing menhir file is highly sensitive to new productions.  After modifying `parser.mly` always run `dune build` and watch for shift/reduce or reduce/reduce conflicts printed by Menhir – these are the primary indicators that your new syntax has introduced ambiguity.
  - Check `docs/design.md` after semantic changes; the design doc is treated as authoritative documentation and should reflect new behaviour.
  - Leave TODO comments in place only if they still make sense; remove stale ones as you touch code.
  - Pay special attention to `frame`, `closure` and `slot` structures – invariants around `depth` and `pure/const` flags drive many invariants in const‑eval.
  - When in doubt, run `grep -n "TODO" lib` and `grep -R "const_types_equal"` to see related code paths.
  - The reviewer should be comfortable with OCaml pattern matching and Menhir grammars, and know to search for `BoundIdentifier` / `BoundLet` when examining value binding logic.

Adding a dedicated section here keeps the project‑specific review guidance alongside other meta‑notes; you can also copy portions into PR templates if needed.
