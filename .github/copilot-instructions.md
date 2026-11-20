# Rampart — Copilot instructions

Short, actionable notes to help AI agents contribute to Rampart (OCaml/Dune).

- **Big picture:** Rampart is an OCaml library + small executable built with Dune. The parser is written with Menhir (`lib/parser.mly`) and the lexer with ocamllex (`lib/lexer.mll`).

- **Build & test (common commands):**
  - Build: `dune build`
  - Run tests: `dune runtest`
  - Run the executable: `dune exec -- rampart` (public executable defined in [bin/dune](bin/dune))
  - Generate opam (handled by Dune): `dune build -p rampart` / see `dune-project` and `rampart.opam` for packaging details.

- **Key files to read before edits:**
  - [dune-project](dune-project) — project metadata and tool versions (Menhir).
  - [lib/dune](lib/dune) — build rules: menhir, ocamllex, ppx, inline_tests.
  - [lib/parser.mly](lib/parser.mly) and [lib/lexer.mll](lib/lexer.mll) — grammar and lexer.
  - [test/parser/expression.ml](test/parser/expression.ml) - parser unit tests.
  - [bin/dune](bin/dune) and `bin/main.ml` — sample executable entry point.

- **Project-specific conventions & gotchas:**
  - Many files are preprocessed; you'll see `.pp.ml` variants generated. Do not edit generated `.pp.ml` files; edit the source (`.ml`, `.mly`, `.mll`) and run `dune build`.
  - Inline tests and expectations are enabled (`ppx_inline_test`, `ppx_expect`). Use `dune runtest` to execute them.

- **When editing grammar/lexer:**
  - Edit `lib/parser.mly` / `lib/lexer.mll` and run `dune build` to regenerate parser artifacts. Menhir flags are defined in [lib/dune](lib/dune).

- **Testing & debugging tips:**
  - All test names should begin with the word "it", where "it" identifies the module being tested.
  - Inspect generated artifacts under `_build/default` to debug preprocessing or parser output (e.g., `_build/default/lib/parser.pp.ml`).

- **Dependencies & tools:**
  - Requires Dune >= 3.20 (see `dune-project`). Menhir and ocamllex are used; ensure Menhir is available when editing grammar.

- **Code‑review checklist (project‑specific):**
  - Ensure `dune build`/`dune runtest` succeed; many edits show up only as expectation mismatches.
  - Leave TODO comments in place only if they still make sense; remove stale ones as you touch code.

