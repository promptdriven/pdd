# PR #1015 — Verification Verdict

**PR:** [feat: add public surface and test churn gates to pdd sync (#1012)](https://github.com/promptdriven/pdd/pull/1015)
**Branch:** `change/issue-1012` → `main`
**Reviewed commit:** `7e1a610aca37230002ae733c0eea2037b03c0a46`
**Verification date:** 2026-05-22
**Worktree:** `/private/tmp/pdd-pr1015-fullverify` (Python 3.13.12 venv)

## Necessity — confirmed

Issue #1012 cites a real production incident: PR #1010 collaterally rewrote
`pdd/update_main.py` + `tests/test_update_main.py` and broke `git`,
`read_fingerprint`, `calculate_sha256`, `derive_basename_and_language`, and
`.pddrc` strength handling. This PR ships the targeted defensive scaffolding
(public-surface + test-churn gates with anchored `BREAKING-CHANGE:` opt-out)
that would have caught that incident pre-merge. The PR is necessary.

## What was checked

| # | Check | Result |
|---|-------|--------|
| 1 | Local branch is identical to upstream PR HEAD | 0 commits ahead / 0 behind |
| 2 | 9/9 GitHub CI checks SUCCESS on `7e1a610a` | Run Unit Tests 8m55s, Public CLI Regression 2m38s, Package Preprocess Smoke 1m24s, Analyze (actions/js-ts/python), CodeQL, heal 5m30s, auto-heal 5m23s |
| 3 | Focused gate-bearing pytest layer (8 files) | 983 passed, 1 skipped, 0 failed |
| 4 | 12-scenario gate matrix via `scenario_matrix.py` | 12/12 PASS |
| 5 | Iter-13 (empty-generation) contract — writer-path tests | 3/3 PASS (`test_empty_generation_over_existing_module_raises_public_surface`, `test_empty_generation_over_existing_test_raises_test_churn`, `test_empty_generation_over_existing_non_python_file_raises_safety_guard`) |
| 6 | Iter-14 (stub kwarg) contract | `tests/test_e2e_issue_342_syspath_isolation.py` 4/4 PASS |
| 7 | Iter-14 (regression-script env flags) — mechanical check | `PDD_SKIP_TEST_CHURN_GATE=1 PDD_SKIP_PUBLIC_SURFACE_GATE=1` exported at top of both `tests/regression.sh` (L53-54) and `tests/cloud_regression.sh` (L54-55), before any pdd invocation |
| 8 | Regression-vs-`origin/main` — 5 failing files diff'd | 12 failed, 231 passed on **both** branches; identical failure names; failures are pre-existing macOS env quirks (PDD_PATH, case sensitivity) |
| 9 | Error-message readability | `PublicSurfaceRegressionError` lists removed/signature_changed symbols + pre/post surface sizes; `TestChurnError` lists ratio + threshold + line counts |

## 12-scenario gate matrix (task #8 detail)

```
1  first-time gen, no existing file              PASS  Gates correctly skipped
2  identical content regenerated                 PASS  Gates correctly silent
3  remove public symbol                          PASS  Lists missing symbols
4  remove _private symbol                        PASS  Private-symbol exemption holds
5  BREAKING-CHANGE: remove (anchored opt-out)    PASS  Anchored directive opts out
6  BREAKING-CHANGE in prose only                 PASS  Anchor-only parser ignores prose
7  test file rewritten >40%                      PASS  TestChurnError fires
8  PDD_TEST_CHURN_THRESHOLD=0.99                  PASS  Env raises ceiling
9  PDD_SKIP_PUBLIC_SURFACE_GATE=1                 PASS  Bypasses gate
10 empty .py gen (iter-13)                       PASS  PublicSurfaceRegressionError + file restored
11 empty .yaml gen (safety guard)                PASS  click.UsageError + file untouched
12 PDD_ALLOW_EMPTY_GENERATION=1                   PASS  Disables safety guard
```

## Local pytest pass/fail (CI-equivalent suite)

```
PR branch (7e1a610a): 59 failed, 9080 passed, 34 skipped, 133 deselected, 1 xfailed  (847.98s)
main      (2e5801ea): 59 failed, 8853 passed, 33 skipped, 133 deselected, 1 xfailed  (674.33s)
delta:                 0 new fails, +227 passes, +1 skip
```

**Both branches show the same 59 failures with the same names.** The PR adds
+227 passing tests (the new gate-coverage suites: `test_one_session_sync.py`,
`test_sync_orchestration.py`, `test_cmd_test_main.py`, `test_agentic_test_generate.py`,
`test_agentic_sync_runner.py`, `test_sync_main.py`, `test_maintenance.py`, and
the expanded `test_code_generator_main.py`).

The 59 failures concentrate in 5 files: `test_postprocess_0.py`,
`test_sync_code_main.py`, `test_sync_order.py`, `test_update_main.py`,
`test_user_story_tests.py`. **None** of these is in PR #1015's diff. Failures
are pre-existing macOS-specific quirks (PDD_PATH not set, case-sensitive
PRD.md vs prd.md, lisp module-extraction regex). GitHub CI runs on Linux and
reports the same suite as **green** (8m55s). **0 net regressions.**

## Non-blocking flags for the merger

1. **40% default test-churn threshold is aggressive enough that normal
   `pdd test` runs against small fixtures will trip it.** That is why iter-14
   had to add `PDD_SKIP_TEST_CHURN_GATE=1` to both regression scripts. Greg/owner
   should be aware of this trade-off when evaluating the default — the gate is
   working as designed, but the default is opinionated.
2. **`mergeStateStatus: BLOCKED` is branch protection** (owner approval
   required), not a technical block. All 9 status checks are SUCCESS.

## Verdict

All named risks tested. 0 regressions in PR-touched code. Gates behave per the
documented contract under the full 12-scenario matrix. 9/9 GitHub CI checks
green. Iter-13 (empty-generation truncation fix) and iter-14 (cloud-test stub +
regression-script skip flags) are both verified end-to-end locally.

**Ready for owner approval.**
