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
| **Invariant-heavy logic** *(parsers, serializers, state machines, sorting/graphs, math/quotas, untrusted inputs)* | Add **>= 1 spec-derived property/fuzz test** (roundtrip, idempotency, conservation, monotonicity, or crash-freedom via `fast-check`, `Hypothesis`, or a deterministic seeded loop) derived from the prompt/Story *before* reading implementation details. |
| **`kind: native-only` / OS-boundary code** | Executable, non-mocked real-host probes (nested OS sandbox child execution, real `/dev/tty` UID/permissions, multi-turn Turn 1 → Turn 2 CLI state, payloads `> 4 KiB`). Mocked-only shells never prove OS boundaries. |
| **CLI apps** | Native integration tests spawning the real entry binary (and optionally `pdd test --target code` only when the prompt declares a CLI runtime interface). |

## 4. Deliberate-Break Probe ("1-to-3 Line Mutation Check")

For medium/big changes (and Autopilot validation), the Fresh Verifier or Reviewer runs a fast, zero-dependency, polyglot mutation check:

1. Pick **1–3 changed non-trivial logic conditions or return values** in the diff.
2. Temporarily flip one condition/return in a scratch edit.
3. Run the PR's tests and confirm **>= 1 assertion fails** (a syntax crash does not count).
4. Immediately revert the scratch edit and re-verify green.

If a repository already runs a mutation tool (`cargo mutants --in-diff`, `stryker --incremental`), configure optional `lint.mutation_command` in `pdd.json`.

## 5. Offline lint, live smoke, independent review & honest disclosure

- **Offline lint:** run `pdd lint` and `pdd lint --diff` (spotlights deleted/skipped/weakened tests, snapshot churn, and `scripts.test`/harness edits).
- **Live local smoke:** run safe local live checks (real CLI command, local dev server + browser, or local test DB) plus the full or sibling native suite. **Ask the person before touching personal credentials or live external accounts.**
- **Independent verification (Smart Subagent Rule):**
  - Pass **only clean file paths** (prompt, Story, `git diff`, `pdd lint --diff` output, real test & live smoke outputs) to the Fresh Verifier and Blind Read-Only Reviewer — **zero Builder chat history**.
  - Check Story AC1 real user surface, 1-to-1 criterion coverage, Deliberate-Break Probe result, and whether an empty stub or signature-only change could pass.
- **Honest `Not proved:` disclosure:** Report exact commands run and real outputs. Explicitly list anything not verified live under `Not proved: <item> (<reason>)` — never imply a simulated or mocked check proved live runtime behavior.
