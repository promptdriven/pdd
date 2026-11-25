# Code-bound formal verification and mutation control

Run code-bound formal/property checks whenever a PR touches rules or state transitions, parsers/validators/serializers, auth/permissions/trust boundaries, money/counts/metrics/math, locking/dedup/scheduling, any prompt/Story with explicit rules (`## Rules to check` / `## Domain decisions`), or any production module that already has an existing formal test.

Skip as **`not-applicable`** (zero busywork) on docs, copy/layout/styling, pure glue/config, or simple CRUD with no invariants. Every formal claim must bind to **real production code** — never standalone spec models.

## 1. Zero-install default and 3-tier code-bound stack

| Tier | When to use | Tools and scope |
|---|---|---|
| **Tier 1 — Zero-install default** | Any PR triggering formal/property checks | **Zero installs required:** use the repo's already-installed property library (`fast-check`, `Hypothesis`, `proptest`, `rapid`) if present; **otherwise write a small deterministic seeded PRNG fuzz loop (e.g. `mulberry32` over 200+ generated worlds) or finite exhaustive small-domain grid directly against real production code** — works in JS/TS, Python, Go, Rust, Java, Ruby, and C++ in milliseconds with zero new dependencies. Pair with strict static typing and real stores (never fake CAS, locks, or revocation in memory). |
| **Tier 2 — Code-bound solver / concurrency** *(opt-in)* | Pure integer math or concurrent protocols where Tier 1 is not enough | `CrossHair` (`hypothesis-crosshair` on pure integer minor-unit Python; note CPython `_decimal`/`sqlite3` limits) or `Kani` (Rust) for genuine code-bound SMT (`proved_solver_code`); `Quint` / `TLA+` **paired with ITF conformance replay or TLC trace validation** against production code for concurrent protocols. Configure custom languages or solvers via merge-base `verify.formal_command` in `pdd.json`. |
| **Tier 3 — Verified kernels** *(opt-in)* | Critical pure kernels verified by construction | `Dafny` (`--target:py`/`--target:js`). Avoid standalone Lean 4 or Bend 2 for general application codegen. |

**Zero-install naming conventions** (auto-discovered and run in per-file subprocess isolation by `pdd prove` and Autopilot):
- JS/TS: `test/*.formal.test.{mjs,js,ts}` — Python: `tests/test_formal_*.py`, `*_formal_test.py`, `formal/test_*.py` — Go: `*_formal_test.go` — Rust: `tests/*formal*.rs` — Any other language/solver: `verify.formal_command` in merge-base `pdd.json`.

## 2. Hard bans and Z3 CI safety

- **Never** claim `proved_solver_code` (or `bounded` / `Proved (solver)`) for hand-written Z3 or math spec models disconnected from production code or near-tautological `UNSAT(And(A, B) & Not(A))` restatements. Any formal file that does not import/reference real production code is strictly **`proved_spec_model`** and never satisfies code verification.
- Whenever Z3 is used in Python, isolate every test/file with its own subprocess, `ctx = z3.Context()`, `z3.Solver(ctx=ctx)`, and an explicit `s.set("timeout", ...)` budget so combined-CI runs cannot deadlock on Z3's global `main_ctx()`.

## 3. Formal mutation control and Rule Coverage table

- **Formal mutation control:** Temporarily mutate 1–3 logic conditions or return values in the target production code and run the **formal suite itself** (never substitute `test_vectors`). Confirm at least 1 assertion fails (a syntax crash does not count), then revert and re-verify green. Required before claiming `proved_solver_code`.
- **Rule Coverage & `Not proved:` table:** Report every touched `.prompt.md` `## Domain decisions` rule and Story `## Rules to check` row alongside its actual verification tier (`Tier 1 zero-install PRNG/grid`, `Tier 1 PBT`, `Tier 2 proved_solver_code`) or an explicit `Not proved: <rule> (<reason>)`.
- **Formal-to-Vector Short JSON export (`Formal ↔ Prompt ↔ Code`):** Serialize shrunk Hypothesis counterexamples, finite boundary grids (`pdd.formal-vectors.v1`), or Quint/Apalache ITF traces (`#meta` + `states`) into `pdd lint`-clean Short JSON companion vectors with `pdd vector export [INPUT] [--entry PATH] [--op OP] [--split] [--out tests/<Story>.<focus>.json] [--write]` (dry-run by default; auto-chunks `> 15` cases with `--split` so exported companions stay within scenario hygiene limits).
