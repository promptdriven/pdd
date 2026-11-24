# Verification, native tests, Feature Maps, and `pdd prove`

Prompt checks (`pdd test`) prove the **prompt**. Real readiness requires proving the **real user path** against real code in the repository's own test runner and local environment.

## 1. Universal "test the real user path" rule & Feature Map (`pdd.json`)

Every behavior change must prove the real user-facing surface — real CLI invocation, local dev server + HTTP/browser flow, or real integration boundary — never mocked-only stubs.

Maintain the repository **Feature Map** in `pdd.json` under `verify`:

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
- `run`: repo-native verification command exercising the real user path. Reference verification scripts by repository-relative path (for example `node scripts/verify.mjs`) so Autopilot Check 4 protects them automatically.
- `needs`: open capability strings (`tty`, `browser`, `docker`, `ios-simulator`, `account:<name>`, custom).
- When adding or changing a user-facing surface, add or update its `verify.paths` entry so `pdd status` shows it. Note: `pdd prove` trusts `verify` recipes from the merge base (`base:pdd.json`), so a newly proposed recipe is exercised locally on its introducing PR and becomes trusted for `pdd prove` once reviewed and merged to the base branch.

## 2. Single exit command: `pdd prove`

- **General exit check:** run `pdd prove [--base REF] [--timeout MIN] [--json]`. It runs offline diff lint, the declared repo test command, merge-base trusted `verify.paths` recipes, and code-bound formal checks (`*.formal.test.*`, `test_formal_*.py`, `*_formal_test.py`, `formal/test_*.py`, `*_formal_test.go`, `tests/*formal*.rs`, or merge-base `verify.formal_command`), reporting **`Proved`** (exit 0), **`Failed`** (exit 1), or **`Not proved`** (exit 3 — missing recipe, missing capability, untrusted config edit, disconnected `proved_spec_model`, timeout, or test-integrity regression) along with a clear `Formal:` status (`not-applicable` on docs/UI/CRUD PRs).
- **Bug-contrast proof:** `pdd prove --base REF --test CMD --expect TEXT [--overlay GLOB] [--setup CMD] [--json]` verifies the regression test fails with the defect symptom on unpatched base code and passes on head code.

## 3. Native test strategy by work kind

| Work kind | Required native verification |
|---|---|
| **Feature** | Interface and integration tests in the repo's native runner (`node:test`, Vitest, Jest, pytest, `go test`, `cargo test`, Playwright) translating every approved Story acceptance criterion **1-to-1**, with unchanged-state / `0`-write assertions on negative rules. |
| **Bug fix** | **Red→Green TDD:** write the failing regression test first against unpatched code → observe the real failure matching the bug's symptom → state `Defect:` and `Not caught because:` → apply root fix → observe pass (and verify with `pdd prove --base ... --test ... --expect ...`). |
| **Rules, invariants & formal-tested modules** *(state transitions, parsers/validators, auth/trust, math/metrics/money, locking/scheduling, `## Rules to check` / `## Domain decisions`, or modules with existing formal tests)* | Load [formal.md](formal.md): use an installed property library or a **zero-install seeded PRNG / finite exhaustive grid** directly against real production code (skip as `not-applicable` on docs/UI/glue/simple CRUD). |
| **`kind: native-only` / OS-boundary code** | Executable, non-mocked real-host probes covering the actual boundary: live HTTP auth/CSRF/path-traversal/forged-body rejection, strict input coercion, real parsers, live CLI-to-server wiring, nested OS sandbox child execution, real `/dev/tty` permissions, multi-turn Turn 1 → Turn 2 CLI state, and payloads `> 4 KiB`. Mocked-only shells never prove OS or transport boundaries. |
| **CLI apps** | Native integration tests spawning the real entry binary (plus optional `pdd test --target code` when the prompt declares a CLI runtime interface). |

## 4. Independent verification, Deliberate-Break Probe, and honest disclosure

- **Offline lint:** run `pdd lint` and `pdd lint --diff` (flags deleted/skipped/weakened tests, snapshot churn, and `scripts.test`/harness edits).
- **Live local smoke:** run safe local live checks (real CLI command, local server/browser, or local test DB) plus the native suite. **Ask the person before touching personal credentials or live external accounts.**
- **Writable Fresh Verifier + Deliberate-Break Probe:** On non-trivial changes, run a writable Fresh Verifier (in a separate session with clean file paths only — prompt, Story, `git diff`, `pdd lint --diff`, real test outputs, zero Builder chat history). Have it perform a fast **Deliberate-Break Probe**: temporarily flip 1–3 changed logic conditions or return values in production code, run the PR's tests, confirm at least 1 assertion fails (a syntax crash does not count), then revert and re-verify green.
- **Blind Read-Only Reviewer:** Give a read-only reviewer strictly clean file paths (`git diff`, owning prompts/Stories, harness outputs, and the Verifier's Deliberate-Break Probe result — zero Builder chat history). A read-only reviewer never edits files; it inspects every changed Story in full (including fenced code blocks, flagging pasted implementation code or internal plumbing as must-fix before approval while allowing exact user-visible values and short examples; move details to `.prompt.md` and large fixtures to `tests/` or `fixtures/`), and checks AC1 real user surface, 1-to-1 criterion coverage, and whether an empty stub or weakened test could pass.
- **Honest `Not proved:` disclosure:** Report exact commands run and real outputs. Explicitly list anything not verified live under `Not proved: <item> (<reason>)` — never imply a simulated or mocked check proved live runtime behavior.
