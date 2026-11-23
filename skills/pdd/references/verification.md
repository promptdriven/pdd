# Verification, native tests, Feature Maps, and `pdd prove`

Prompt checks (`pdd test`) prove the **prompt**. Real implementation readiness requires proving the **real user path** against real code in the repository's own test runner and local environment.

## 1. Universal "test the real user path" rule & Feature Map (`pdd.json`)

Every behavior change must prove the real user-facing path — real CLI invocation, local dev server + browser/HTTP request, or real integration boundary — never mocked-only stubs.

Maintain the repository **Feature Map** inside `pdd.json` under `verify`:

```json
{
  "verify": {
    "test": "npm test",
    "paths": [
      {
        "id": "cli-status",
        "name": "CLI offline status overview",
        "when": ["src/core/status.mjs", "src/pdd-cli.mjs"],
        "run": "node bin/pdd.mjs status --json",
        "needs": []
      }
    ]
  }
}
```

- `when`: path globs covering direct and indirect files that affect that user path.
- `run`: repo-native verification command exercising the real user path.
- `needs`: open capability strings (`tty`, `browser`, `docker`, `ios-simulator`, `account:<name>`, custom).
- Whenever you add or change a user-facing surface, add or update its `verify.paths` entry so `pdd status` displays it and `pdd prove` runs it automatically.

## 2. Single exit command: `pdd prove`

- **General PR exit check:** run `pdd prove [--json]` against the default-branch merge base. It runs offline diff lint, the declared repo test command, and touched `verify.paths` recipes, reporting three distinct states: **`Proved`**, **`Failed`**, or **`Not proved`** (missing recipe or missing capability).
- **Bug-contrast proof:** `pdd prove --base REF --test CMD --expect TEXT [--overlay GLOB] [--setup CMD] [--json]` verifies the regression test fails for the exact bug symptom on unpatched base code and passes on head code.

## 3. Native test strategy by work kind

| Work kind | Required native verification |
|---|---|
| **Feature** | **Testing Trophy** interface/integration tests in the repo's native runner (`Node`/`Vitest`/`Jest`/`Pytest`/`Go`/`Cargo`/`Playwright`), translating every approved Story acceptance criterion **1-to-1** (with unchanged-state / `0`-write assertions on negative rules). Skip micro-TDD theater on greenfield features. |
| **Bug fix** | **Mandatory Red→Green TDD:** write the failing regression test first against unpatched code → observe the real failure matching the bug's exact symptom → state `Defect:` and `Not caught because:` → apply root fix → observe pass. |
| **Invariant-heavy logic** *(parsers, serializers, state machines, sorting/graphs, math/quotas, untrusted inputs)* | Follow the **3-tier code-bound verification stack** below: default **Tier 1** strict typing + stateful property-based testing + real-store exhaustive grids; **Tier 2** code-bound SMT / trace-checked concurrency only when justified; **Tier 3** opt-in verified kernels. |
| **`kind: native-only` / OS-boundary code** | Executable, non-mocked **adversarial & interactive real-host probes**: live HTTP auth/CSRF/path-traversal/SSRF/forged-body rejection, strict input coercion (rejecting e.g. `bool("false")`), real binary/document parsers, live CLI-to-server wiring, nested OS sandbox child execution, real `/dev/tty` UID/permissions, multi-turn Turn 1 → Turn 2 CLI state, and payloads `> 4 KiB`. Mocked-only shells never prove OS or transport boundaries. |
| **CLI apps** | Native integration tests spawning the real entry binary (and optionally `pdd test --target code` only when the prompt declares a CLI runtime interface). |

## 4. Three-tier code-bound formal verification & mutation control

When verifying invariants, bind proofs to **real production code** — never standalone spec models:

- **Tier 1 (Default mandatory for invariant-heavy code):** Strict static typing (`pyright`/`mypy --strict`, Pydantic `StrictBool`) + real-code stateful property-based testing (`Hypothesis` `RuleBasedStateMachine` over real SQLite/FastAPI for Python, `fast-check` `fc.commands` for JS/TS, `proptest` for Rust, `rapid` for Go) + finite exhaustive grids over real stores (never fake CAS, locks, or revocation in memory).
- **Tier 2 (Code-bound solver / concurrency):** `CrossHair` (`hypothesis-crosshair` on pure integer minor-unit Python math; note CPython `_decimal`/`sqlite3` limits) or `Kani` (Rust) for genuine code-bound SMT (`proved_solver_code`); `Quint` / `TLA+` **strictly paired with ITF conformance replay or TLC trace validation** against production code for concurrent protocols.
- **Tier 3 (Opt-in verified kernels):** `Dafny` (`--target:py`/`--target:js`) when verified-by-construction pure kernels are required. Avoid standalone Lean 4 or Bend 2 for general application codegen.
- **Hard bans & Z3 CI safety:**
  - **Never** claim `Proved (solver)` for hand-written Z3 spec models disconnected from production code or near-tautological `UNSAT(And(A, B) & Not(A))` restatements (`proved_spec_model` never satisfies code verification).
  - Whenever Z3 is used in Python, isolate every test/file with `ctx = z3.Context()`, `z3.Solver(ctx=ctx)`, and an explicit `s.set("timeout", ...)` budget (prevents Z3 `main_ctx()` combined-CI deadlocks).
- **Deliberate-Break Probe ("1-to-3 Line Mutation Check") & formal mutation control:** For medium/big changes (and Autopilot validation), pick **1–3 changed non-trivial logic conditions or return values** in production code, temporarily flip one condition/return in a scratch edit, run the PR's tests — and for formal claims, run the **formal suite itself** (never substitute `test_vectors`) — confirm **>= 1 assertion fails** (a syntax crash does not count), then revert and re-verify green. Optional repo-wide mutation tool: `lint.mutation_command` in `pdd.json`.
- **Rule Coverage & `Not proved:` table:** For invariant-heavy or formal work, report every touched `.prompt.md` `## Domain decisions` rule and Story `## Rules to check` row with its concrete test/proof tier or explicit `Not proved: <rule> (<reason>)`.

## 5. Offline lint, live smoke, independent review & honest disclosure

- **Offline lint:** run `pdd lint` and `pdd lint --diff` (spotlights deleted/skipped/weakened tests, snapshot churn, and `scripts.test`/harness edits).
- **Live local smoke:** run safe local live checks (real CLI command, local dev server + browser, or local test DB) plus the full or sibling native suite. **Ask the person before touching personal credentials or live external accounts.**
- **Independent verification (Smart Subagent Rule):**
  - Pass **only clean file paths** (prompt, Story, `git diff`, `pdd lint --diff` output, real test & live smoke outputs) to the Fresh Verifier and Blind Read-Only Reviewer — **zero Builder chat history**.
  - Check Story AC1 real user surface, 1-to-1 criterion coverage, Deliberate-Break Probe result, and whether an empty stub or signature-only change could pass.
- **Honest `Not proved:` disclosure:** Report exact commands run and real outputs. Explicitly list anything not verified live under `Not proved: <item> (<reason>)` — never imply a simulated or mocked check proved live runtime behavior.
