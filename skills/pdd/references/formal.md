# Code-bound formal verification and mutation control

Load this reference **only** for invariant-heavy work (parsers, serializers, state machines, schedulers, graphs, money/quota math, concurrency, or untrusted inputs). Every formal claim must bind to **real production code** — never standalone spec models.

## 1. Three-tier code-bound stack

| Tier | When to use | Tools and scope |
|---|---|---|
| **Tier 1 (Default)** | Any invariant-heavy production module | Strict static typing (`pyright`/`mypy --strict`, Pydantic `StrictBool`, TypeScript `strict`) + real-code stateful property-based testing (`Hypothesis` `RuleBasedStateMachine` over real SQLite/FastAPI for Python, `fast-check` `fc.commands` for JS/TS, `proptest` for Rust, `rapid` for Go) + finite exhaustive grids over real stores (never fake CAS, locks, or revocation in memory). |
| **Tier 2 (Code-bound solver / concurrency)** | Pure integer math or concurrent protocols where Tier 1 is not enough | `CrossHair` (`hypothesis-crosshair` on pure integer minor-unit Python; note CPython `_decimal`/`sqlite3` limits) or `Kani` (Rust) for genuine code-bound SMT (`proved_solver_code`); `Quint` / `TLA+` **paired with ITF conformance replay or TLC trace validation** against production code for concurrent protocols. |
| **Tier 3 (Opt-in verified kernels)** | Critical pure kernels verified by construction | `Dafny` (`--target:py`/`--target:js`). Avoid standalone Lean 4 or Bend 2 for general application codegen. |

## 2. Hard bans and Z3 CI safety

- **Never** claim `proved_solver_code` (or `Proved (solver)`) for hand-written Z3 spec models disconnected from production code or near-tautological `UNSAT(And(A, B) & Not(A))` restatements. Standalone spec models are `proved_spec_model` and never satisfy code verification.
- Whenever Z3 is used in Python, isolate every test/file with its own `ctx = z3.Context()`, `z3.Solver(ctx=ctx)`, and an explicit `s.set("timeout", ...)` budget so combined-CI runs cannot deadlock on Z3's global `main_ctx()`.

## 3. Formal mutation control and Rule Coverage table

- **Formal mutation control:** Temporarily mutate 1–3 logic conditions or return values in the target production code and run the **formal suite itself** (never substitute `test_vectors`). Confirm at least 1 assertion fails (a syntax crash does not count), then revert and re-verify green.
- **Rule Coverage & `Not proved:` table:** Report every touched `.prompt.md` `## Domain decisions` rule and Story `## Rules to check` row alongside its actual verification tier (`Tier 1 PBT`, `Tier 2 proved_solver_code`, `bounded real-store grid`) or an explicit `Not proved: <rule> (<reason>)`.
