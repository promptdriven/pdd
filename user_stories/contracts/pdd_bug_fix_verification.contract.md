<!-- pdd-story-contract derived-from-story="../story__pdd_bug_fix_verification.md" story-hash="29c6a547ae8cc133" issue-ref="https://github.com/promptdriven/pdd/issues/1769" -->

# Contract: Bug report becomes a verified fix

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_bug_fix_verification.md`), not this contract.

## Covers

- R1: Bug issue URLs route through `pdd bug` to create a reproducible failing test or test plan.
- R2: The bug workflow distinguishes code bugs from prompt defects before the fix loop runs.
- R3: `pdd fix` consumes the failing tests and protected context as repair constraints.
- R4: The fix workflow iterates until local verification passes or a clear failure is reported.
- R5: Post-fix evidence preserves test results, CI status when enabled, and workflow comments.
- R6: The cross-dev-unit story is attributed to analysis, bug orchestration, fix command, E2E fix orchestration, and shared agentic utilities without duplicate global counting.

## Context

The documented bug workflow starts with `pdd bug <issue-url>` to create failing
tests, then uses `pdd fix <issue-url>` to repair code until tests pass locally
and, when enabled, through post-push CI. This crosses the analysis command,
bug orchestrator, fix command, E2E fix orchestrator, and shared agentic
comment/evidence utilities.

## Acceptance Criteria

1. Given a GitHub bug issue, when the user runs `pdd bug <issue-url>`, then PDD routes to the agentic bug workflow and captures the observed failure as executable or planned regression evidence.
2. Given the root cause indicates a prompt defect, when the bug workflow classifies the defect, then it records that the prompt must be fixed before generating downstream tests.
3. Given failing tests exist for the bug, when the user runs `pdd fix <issue-url>`, then PDD uses those tests as constraints for the repair loop.
4. Given tests fail after a repair attempt, when the fix loop continues, then the workflow reports the failure and attempts another bounded repair rather than declaring success.
5. Given local verification passes, when the workflow finishes, then the PR evidence identifies the tests and any CI validation or skipped CI choice.
6. Given coverage reports this story, when bug and fix dev units are listed separately, then this story appears under each linked unit but is counted once globally.

## Oracle

These details matter for pass/fail:
- `pdd bug` routes issue URLs to bug reproduction
- failing tests or explicit test plan evidence are created before repair
- prompt-defect classification is not lost
- `pdd fix` uses tests as constraints and verifies before success
- post-fix evidence includes local checks and CI status or skip reason
- cross-unit metadata lists every participating dev unit

## Non-Oracle

These details should not matter:
- exact generated test code
- exact repair patch content
- exact provider/model used
- exact comment formatting beyond status and evidence semantics

## Negative Cases

- `pdd fix` must not declare success while the captured failing tests still fail.
- A prompt defect must not be treated as only a generated-code bug when the workflow has enough evidence to classify it.
- CI failures must not be hidden when CI validation is enabled.
- Coverage must not count this one cross-unit story once for each linked prompt.

## Non-Goals

- This story does not prescribe the exact unit tests produced by `pdd bug`.
- This story does not cover feature-request handling through `pdd change`.
- This story does not require live CI in deterministic local verification.

## Candidate Prompts

- `prompts/commands/analysis_python.prompt` - owns the public `pdd bug` command surface.
- `prompts/agentic_bug_orchestrator_python.prompt` - owns bug workflow orchestration.
- `prompts/commands/fix_python.prompt` - owns the public `pdd fix` command surface.
- `prompts/agentic_e2e_fix_orchestrator_python.prompt` - owns iterative fix verification.
- `prompts/agentic_common_python.prompt` - owns shared agentic comments and runner behavior.
- `prompts/agentic_bug_python.prompt` - related bug workflow behavior.

## Notes

This story is a cross-dev-unit regression oracle for the documented
bug-to-fix workflow in `docs/TUTORIALS.md` and `docs/prompting_guide.md`.
