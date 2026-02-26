# Rampart — Copilot instructions

Short, actionable notes to help AI agents contribute to Rampart (OCaml/Dune).

- **Big picture:** Rampart is an OCaml library + small executable built with Dune. The parser is written with Menhir (`lib/parser.mly`) and the lexer with ocamllex (`lib/lexer.mll`). The runtime/evaluator lives in `lib/evaluate.ml` and implements a small scheduler using OCaml effects (`Effect.Deep`) with custom `Fork` and `Defer` effects.

- **Build & test (common commands):**
  - Build: `dune build`
  - Run tests: `dune runtest`
  - Run the executable: `dune exec -- hello` (public executable defined in [bin/dune](bin/dune))
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
  - Use `dune build` then `dune exec -- hello` to exercise the runtime.
  - Inspect generated artifacts under `_build/default` to debug preprocessing or parser output (e.g., `_build/default/lib/parser.pp.ml`).
  - Runtime errors raise `Located_error` with location info — check `lib/diagnostic.ml`/`lib/error.ml` for error formatting.

- **Dependencies & tools:**
  - Requires Dune >= 3.20 (see `dune-project`). Menhir and ocamllex are used; ensure Menhir is available when editing grammar.

- **PR guidance for changes touching core evaluator or grammar:**
  - Add or update tests under `test/` or `lib/` inline-tests.
  - Keep changes small and preserve existing scheduling/deferral semantics in `lib/evaluate.ml` unless intentionally replacing the scheduler; include tests that exercise `Defer` behavior to avoid regressions.
