# Issue #2026 controlled comparison report

Date: 2026-07-13 (America/Los_Angeles)

## Conclusion

The requested agentic-versus-regular comparison is **still blocked**. The attempted paired `--dry-run` arms are not a valid mode comparison: `sync_main()` branches on `dry_run` before normal synchronization, and `sync_orchestration()` then displays an existing sync log before any regular/agentic behavior can diverge. With no logs in the fixture, both arms exercised the same prompt-discovery/log-display path and printed `No sync log found`.

The run did produce trustworthy, zero-provider evidence for two narrower claims: the exact fixture-#7 regression in #1980 changes from 1/2 to 2/2 issue-scope recall at pinned non-main SHA `f680c761462160ecdaec7b550be26ea529024801`, and #1979's focused regressions pass on that candidate lineage. The six paired arms are retained only as a network-isolated parity smoke test of the shared dry-run path, not as comparison evidence.

The fixture task itself was not implemented by either arm because every execution was `--dry-run`. Therefore code correctness, generated patch quality, generated-code tests, generation token parity, and real-generation cost parity are **not measured**.

Implementation issue #2028 tracks the required hermetic write-mode harness that must prove distinct mode-specific code paths before this comparison can be completed.

For default/main claims, #1979 and #1980 are still open and their fixes are not on `main`. #1979 is corrected and tested on epic SHA `263b4925...`; the exact #1980 fixture regression is corrected and tested only at open PR #1983 head `f680c761...`. These defects are controlled at the pinned candidate, not released or generally proven fixed.

## Correctness blocker status

| Defect | Current evidence | Benchmark status |
|---|---|---|
| #1979, failed single-module sync exits 0 | PR #1982 merged into the non-main epic branch; candidate inherits it. Nine focused tests pass, including failure exit, dry-run exit, evidence/cost preservation, and stream cleanup. | Fixed/controlled at candidate SHA; still blocks `main`/default claims until merged. |
| #1980, branch-diff fast path under-scopes issue modules | Historical epic SHA selects only `greeter`, drops `greeter -> textutil`, and reports success. PR #1983 candidate selects both modules and preserves the edge. Fixture-#7 E2E repro plus six focused unit tests pass. | Exact regression corrected/controlled at PR #1983 head; general and `main`/default claims remain blocked while PR is open/unmerged. |

## Planning validation (not the paired execution result)

Actual workload: frozen synthetic issue `https://github.com/e2e-org/greeter-proj/issues/7`, issue JSON SHA-256 `2db0e250c0928de78b1ad7fddf641d97777466d9e8a718072109d7e0c69a7c2e`. It explicitly names `prompts/greeter_python.prompt` and `prompts/textutil_python.prompt`; `architecture.json` declares `greeter -> textutil`.

Both historical and candidate planning observations started from identical modified fixture commit `77df338ea548220bb80a2ec949b779f6b6f2224b` and tree `430920c8ace9e57c22b060ae8925c22fdf3f13a2`, where only the greeter prompt differs from `main`.

| Planning SHA | Scope recall | Dependency recall | Provider calls | Outcome |
|---|---:|---:|---:|---|
| Historical `263b4925...` | 1/2 (50%): `greeter` only | 0/1; edge omitted | 0 | Incorrectly reports success for one module. |
| Candidate `f680c761...` | 2/2 (100%): `greeter`, `textutil` | 1/1; edge preserved | 0 | Reports both modules would sync. |

There is no regular-sync issue-URL planner in the CLI. Regular mode therefore has no equivalent result in this planning experiment. The issue-level result must not be conflated with the paired module execution below.

## Rejected paired dry-run attempt

Each arm was reconstructed using the fixture constructor in `tests/test_agentic_sync_mocked_e2e.py`, then normalized to the same root commit. State equivalence was strong: all six arms started at commit `3d4a0c82eeb22b2f3f8b97dbe94289123cc66a6c`, tree `29f3d82202e1d648b20449db8efc2a8d0c78288d`, clean status, and the same file hashes:

- `.pddrc`: `0eeaa7e6e6881b1e420f0472ffa643a453e58e68bea6bd1aa364bed721f608bf`
- `architecture.json`: `678cea76276a6e0bbcad731a0ec7179c247d90024c2b327b27b376566fce5da9`
- `prompts/greeter_python.prompt`: `1aa68d69c9999ba9ee1868047ba9df56108744ec7e0d9e6cc40fac62621a8af2`
- `prompts/textutil_python.prompt`: `6d645662492a1089365df78629fe4eaef5a6c980494464378444f443925976e6`

Schedule: `regular, agentic, agentic, regular, regular, agentic` (three AB/BA pairs). Each arm ran `textutil` before `greeter` exactly once, with no retry or manual intervention inside the accepted controlled run.

Regular commands:

```text
/opt/anaconda3/bin/python -m pdd --force --local sync textutil --dry-run --no-steer
/opt/anaconda3/bin/python -m pdd --force --local sync greeter --dry-run --no-steer
```

Agentic commands:

```text
/opt/anaconda3/bin/python -m pdd --force --local sync textutil --dry-run --agentic --no-steer
/opt/anaconda3/bin/python -m pdd --force --local sync greeter --dry-run --agentic --no-steer
```

Fixture #7 was **not** the actual paired execution input: neither command received the issue URL or read the issue JSON. The harness supplied the ordered manifest directly. More importantly, both commands took the same early dry-run path at `pdd/sync_main.py:743-780` and `pdd/sync_orchestration.py:2033-2051`. Therefore the table below describes only a shared-path smoke test.

| Smoke-test evidence | Regular label | Agentic label |
|---|---|---|
| Arms / module commands | 3 / 6 | 3 / 6 |
| Exit results | 6/6 zero | 6/6 zero |
| Hard-coded command manifest | 2/2 in every arm | 2/2 in every arm |
| Tracked files changed | None | None |
| Output patch | Empty | Empty |
| Unexpected files | Two `.pdd/core_dumps/*.json` per arm | Two `.pdd/core_dumps/*.json` per arm |
| Provider CLI calls | 0 | 0 |
| GitHub writes | 0 | 0 |
| Tripwire hits | 0 | 0 |
| Raw arm elapsed seconds (not comparable) | 6.937, 7.458, 6.943 | 7.411, 7.153, 6.667 |

No runtime parity claim is valid. These timings primarily measure interpreter startup, imports, prompt discovery, and log display, not mode-specific synchronization.

## Tests

Scrubbed, OS-network-denied candidate run (abbreviated here; the full `sandbox-exec ... env -i ...` invocation is preserved in the issue update and reproduction artifacts):

```text
python -m pytest -q tests/test_agentic_sync_mocked_e2e.py tests/test_issue_1979_sync_exit_code.py
```

Result: `14 passed` in 65.10 seconds (five fixture-#7 hermetic E2E tests and nine #1979 regressions). Separately, six focused #1980 unit tests passed (`269 deselected`).

No generated-code tests were run because dry-run generated no source or test files. This test result validates the fixture regression and #1979, not a paired mode comparison.

## Environment and network controls

- macOS 14.5 (23F79), Apple Git 2.39.5, `/opt/anaconda3/bin/python` 3.13.9.
- Candidate and baseline are detached worktrees; no branch was merged or modified.
- Child environments are constructed from scratch by the frozen harness: restricted `PATH`, empty scratch `HOME`/`TMPDIR`, no inherited API keys/tokens, checkout-pinned `PYTHONPATH`, `PDD_FORCE_LOCAL=1`, `PDD_FORCE=1`, `PDD_AUTO_UPDATE=false`, `PDD_AGENTIC_PROVIDER=anthropic`, `LITELLM_CACHE_DISABLE=1`.
- Local `gh`, `claude`, and child `pdd` shims are first on `PATH`; `codex`, `gemini`, `agy`, and `opencode` are fail-closed tripwires (exit 86).
- Every benchmark process inherited a macOS Seatbelt profile containing `(deny network*)`. Direct external TCP (`1.1.1.1:443`) and loopback TCP (`127.0.0.1:9`) probes both failed with `PermissionError(1, 'Operation not permitted')`.
- LiteLLM attempted its public model-cost-map refresh on import; stderr records DNS/network failure. The OS profile denied the operation before contact. No provider CLI was invoked, and direct provider HTTP would be covered by the same kernel network denial.
- Provider calls are directly observed as zero; token usage is not measured and is reported as N/A. CLI dry-run output printed `$0.000000` estimated cost. The actual controlled run incurred no provider/service charge because no network operation was permitted and no provider invocation occurred.

Separate from the benchmark, GitHub-app jobs automatically attached to #2026 attempted Google OAuth and Anthropic before this local comparison. Issue comments report authentication/credit failures, zero Anthropic tokens, and total cost `0.0`. Those jobs are excluded from all benchmark results; `/pdd stop` was posted at comment `4962818801` to cancel the queued retry.

## Reproduction

```text
git worktree add --detach /private/tmp/pdd-2026-candidate f680c761462160ecdaec7b550be26ea529024801
git worktree add --detach /private/tmp/pdd-2026-baseline 263b4925f1a53b3f1cfe8a15274d2a18af842c17
sandbox-exec -f network-deny.sb /opt/anaconda3/bin/python run_comparison.py --checkout /private/tmp/pdd-2026-candidate --output candidate-f680c761-controlled
sandbox-exec -f network-deny.sb /opt/anaconda3/bin/python run_comparison.py --planning-only --checkout /private/tmp/pdd-2026-baseline --output baseline-263b4925-controlled
```

Primary artifact hashes:

- `run_comparison.py`: `7b0331faea3da3fec79c35f1666e2a37bd54352c404c0f02f9277782b2267a5c`
- `network-deny.sb`: `5c358b8d847211333e7ba22df82d84f796b5f30a41a2682209a949d783adbd08`
- candidate `summary.json`: `401c6970f7200c5ee2d761d8aadcf509930fa90f744a7f224093892f11527ad7`
- baseline `summary.json`: `f362888fcbef55b6d5302a27ef817d22d3c633d74726580bb58cc1e51134e983`
- hermetic JUnit XML: `8a96968a795b679775525e6f595f51adabab5e1c890ab2fba0924d2c112a7022`

## Limitations

1. No valid paired mode comparison was completed. The attempted arms converge on the same early dry-run log-display path.
2. Fixture #7 is genuinely exercised only by the agentic issue-planning observation. The paired smoke test uses a hard-coded manifest and cannot measure issue-scope recall or file selection.
3. Requested implementation completion, generated correctness, generated patches, generated tests, generation tokens, real cost, and mode-specific runtime are unmeasured.
4. Regular sync has no issue-URL planning surface. The agentic planning result is necessarily a separate one-arm experiment.
5. The candidate is an open, unmerged non-main PR head. Results do not establish current `main` behavior or readiness for agentic-by-default rollout.
6. The synthetic fixture has two Python modules and one dependency; conclusions should not be generalized to larger graphs, ambiguous module identities, retries, or write mode.
7. Debug core dumps are symmetric but are still untracked side effects of dry-run.
8. Earlier directories `candidate-f680c761/` and `candidate-f680c761-final/` are exploratory harness-development runs and are excluded. Only `*-controlled/` data is accepted.

## Adversarial review

The independent reviewer found one critical blocker and six supporting findings:

1. Both paired arms execute the same early dry-run log-display implementation; reject them as a mode comparison.
2. Fixture #7 is the actual workload only for agentic planning, not paired execution.
3. Task completion, correctness, patch quality, generated tests, token use, cost parity, and mode-specific runtime are unmeasured.
4. #1980 is corrected only for the exact regression at the pinned open PR head; #1979 is corrected only on the non-main epic lineage.
5. OS network denial and empty provider logs are convincing; no paid/external provider contact was found. Preserve the outer sandbox command/profile hash for provenance.
6. State equivalence within the controlled smoke run is sound, with no asymmetric retry or manual assistance.
7. Exploratory runs must be explicitly excluded.

Verdict: accept the artifacts as fixture-#7 regression evidence plus a network-isolated shared-path smoke test. Reject them as a completed agentic-versus-regular sync comparison.
