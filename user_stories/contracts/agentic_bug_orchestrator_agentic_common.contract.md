<!-- pdd-story-contract derived-from-story="../story__agentic_bug_orchestrator_agentic_common.md" story-hash="164350f683ab848b" issue-ref="https://github.com/promptdriven/pdd/issues/1641" -->

# Contract: pdd-bug: report recoverable step failures as degraded instead of fatal

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__agentic_bug_orchestrator_agentic_common.md`), not this contract.

## Covers
- AC1: Distinguish recoverable step failures from fatal workflow failures in visible comments.
- AC2: Use wording like `Status: DEGRADED - workflow continuing` when a failed step is tolerated.
- AC3: Reserve `Status: FAILED - workflow aborting` for actual terminal failures.
- AC4: For Step 8 specifically, mention that test strategy failed and later test generation will use fallback/default planning.
- AC5: Keep successful later step reports and final PR success behavior intact.
- R1: Add regression coverage for: Step 8 provider failure -> degraded comment -> workflow continues -> final success.
- R2: Add regression coverage for: consecutive/fatal provider failures still post a fatal comment and stop.

## Context
The `pdd bug` command orchestrates a multi-step workflow to generate fixes for GitHub issues. Individual steps can fail due to transient issues (e.g., provider timeouts). The orchestrator can be configured to tolerate certain step failures and continue the workflow in a degraded mode, while other failures are fatal and cause the entire workflow to abort. The user observes the workflow's progress via step comments posted to the GitHub issue.

## Acceptance Criteria
1. Given a `pdd bug` workflow is executing and a non-fatal, recoverable step failure occurs, when the orchestrator posts a comment for that step, then the comment indicates a degraded status and that the workflow is continuing (e.g., `Status: DEGRADED - workflow continuing`).
2. Given a `pdd bug` workflow is executing and a fatal step failure occurs, when the orchestrator posts a comment for that step, then the comment indicates a failed status and that the workflow is aborting (e.g., `Status: FAILED - workflow aborting`).
3. Given a `pdd bug` workflow experiences a recoverable failure in Step 8 (test strategy), when the orchestrator posts the degraded comment for that step, then the comment mentions the test strategy failure and indicates a fallback/default plan will be used for later test generation.
4. Given a `pdd bug` workflow continues after a recoverable step failure, when subsequent steps succeed, then those steps post successful status comments and the workflow can culminate in a final success (e.g., opening a PR with a success comment).

## Oracle
These details matter for pass/fail:
- The visible status keyword in the step comment (`DEGRADED` vs. `FAILED`).
- The indication of workflow continuation or abortion in the comment text.
- For Step 8 recoverable failures, the mention of test strategy failure and fallback planning.
- The preservation of successful step reporting and final workflow success after a degraded step.
- The workflow halting after a fatal step failure.

## Non-Oracle
These details should not matter:
- The exact phrasing beyond the required status keywords and continuation/abortion semantics.
- The specific visual template or formatting of the comment.
- The internal mechanism for determining if a failure is recoverable.
- The specific provider or error that caused the step failure.
- The cosmetic presentation of spinner or control characters in logs.

## Negative Cases
- A workflow that stops after a recoverable failure posts a `FAILED - workflow aborting` comment.
- A workflow that continues after a fatal failure posts a `DEGRADED - workflow continuing` comment.
- A recoverable Step 8 failure comment omits mention of test strategy failure and fallback planning.
- A workflow that continues after a degraded step fails to post successful comments for later steps or cannot reach a final successful outcome.

## Non-Goals
- Sanitizing Claude PTY spinner/control-character timeout tails in the GitHub App runner.
- Improving provider reliability itself.
- Implementing general provider-limit queueing or resume policies.

## Candidate Prompts
- `agentic_bug_orchestrator_python.prompt` — Orchestrates the 12-step bug workflow and owns step comment posting. (primary)
- `agentic_common_python.prompt` — Provides shared agentic CLI execution and the `post_step_comment` fallback template. (primary)
- `agentic_change_orchestrator_python.prompt` — Orchestrates a similar multi-step change workflow; may share step comment semantics. (possible)
- `agentic_e2e_fix_orchestrator_python.prompt` — Orchestrates a similar multi-step E2E fix workflow; may share step comment semantics. (possible)
- `agentic_test_orchestrator_python.prompt` — Orchestrates a multi-step test generation workflow; may share step comment semantics. (possible)

## Notes
- The issue provides concrete evidence links for the problematic behavior in promptdriven/Generative-Video-Studio#792.
- The fix targets specific code areas: `agentic_bug_orchestrator.py`, `agentic_common.py`, and their corresponding test files.
- Regression tests should cover the two key scenarios: single recoverable failure leading to degraded continuation, and fatal/consecutive failures leading to abort.
- The distinction is user-facing and about clear communication, not internal state management.
