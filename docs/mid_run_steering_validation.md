# Mid-run steering validation (#1324)

Foundation (`drain_issue_steers`, `run_agentic_task(..., steers=)`, GET-safe `gh api`
polling) ships in **#1328**. Orchestrator step-boundary wiring ships in **#1336**.

## Automated coverage

Run the integration suite:

```bash
pytest -vv tests/test_mid_run_steer_orchestrator_integration.py
```

Together with the foundation and orchestrator unit tests:

```bash
pytest -q tests/test_mid_run_steer_orchestrator_integration.py \
  tests/test_agentic_common.py -k "steer or drain_issue or seed_issue" \
  tests/test_agentic_test_orchestrator.py -k "steer or clarification" \
  tests/test_agentic_bug_orchestrator.py -k "clarification or steer"
```

### What the integration module asserts

| Scenario | Test |
|----------|------|
| Cursor seeded at workflow start | `test_test_orchestrator_calls_seed_at_start` |
| Seed skipped when cursor already in resumed state | `test_ensure_issue_steer_cursor_seeded_noop_when_resumed` |
| Human comment drained at step boundary → `steers=` | `test_test_orchestrator_e2e_seed_drain_inject_idempotent` |
| Same `comment_id` not injected twice | `test_env_steer_injected_once_on_resume`, idempotent tail of E2E test |
| Bot / state marker / progress comments filtered | `test_drain_filters_bot_state_and_progress_comments` |
| Prompt contains `## Steered user input (mid-run)` | `test_run_agentic_task_injects_steered_section` |
| Empty-issue seed survives save/resume (`steer_cursor_seeded`) | `test_seed_issue_steer_cursor_empty_issue_persists_seed_on_resume` |
| Baseline fetch failure does not set `steer_cursor_seeded` | `test_seed_issue_steer_cursor_does_not_mark_seeded_on_fetch_failure` |
| Baseline fetch failure logs a warning | `test_seed_issue_steer_cursor_warns_on_fetch_failure` |
| Missing `gh` does not set `steer_cursor_seeded` | `test_seed_issue_steer_cursor_missing_gh_does_not_mark_seeded` |
| Failed seed → drain does not ingest historical comments | `test_failed_seed_then_drain_skips_historical_comments` |

## Manual / cloud checklist (before closing #1324)

1. Start an issue-driven workflow (`pdd change`, `pdd bug`, or `pdd test`) with `gh` authenticated.
2. Confirm workflow state gains `steer_cursor_seeded` / `last_steered_comment_id` after start (no historical comments in the first step prompt). If the worker cannot fetch issue comments (missing `gh`, auth/network error, nonzero `gh api`), `steer_cursor_seeded` is **not** set, a warning is logged, and GitHub comment steering stays disabled until a later successful seed.
3. Post a normal human issue comment mid-run (not a bot progress comment).
4. After the current step finishes, confirm the next step’s agent prompt includes **Steered user input (mid-run)** with that comment.
5. Re-run or resume the same workflow; the same comment must **not** appear again.
6. Post `/stop` or remove the job label in **pdd_cloud** — the CLI must **not** treat that as steer input (cancellation is cloud-side).
7. Optional: set `PDD_STEER_JSON` in the worker to simulate cloud handoff; behavior should match GitHub polling.

## #1324 scope status (§2 / §6 / §7)

| Section | Requirement | Status on `change/issue-1324-steer-wiring` |
|---------|-------------|---------------------------------------------|
| **§2** | Steer points in issue orchestrators | **Done** — change, bug, test, e2e_fix, checkup, architecture |
| **§2** | `agentic_split_orchestrator` | **Deferred** — no issue repo coordinates (documented out of scope) |
| **§2** | `sync_orchestration.py` comment steer | **Deferred** — local TUI `maybe_steer_operation` only; not GitHub issue comments |
| **§2** | `agentic_sync` (parallel module sync) | **Partial** — `AsyncSyncRunner` seeds cursor and drains at module boundaries for progress UX; steers are not injected into `pdd sync` subprocess prompts (no `run_agentic_task` on that path) |
| **§6** | Relax `issue_updated_at` staleness | **Done** — change, test, and bug orchestrators use `issue_update_should_clear_workflow_state` |
| **§6** | e2e_fix / checkup staleness | **N/A** — those flows do not compare `issue_updated_at` today |
| **§7** | Progress UX | **Done** — console on drain; `peek_agentic_progress_steer_metadata` + sync runner `github_info` pending-steer line |

## Out of scope for this validation

- `agentic_split_orchestrator` (no issue repo coordinates)
- `sync_orchestration` TUI `maybe_steer_operation` (interactive sync only)
- Mid-token abort inside a single provider subprocess call
- Injecting mid-run steers into `pdd sync` module subprocesses (requires a separate design)
