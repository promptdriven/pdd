<!-- pdd-story-contract derived-from-story="../story__pdd_ci_validation_fix_loop.md" story-hash="1365d18bbb3b0c9c" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: CI failures keep the fix loop honest

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_ci_validation_fix_loop.md`), not this contract.

## Covers

- R1: Post-push CI validation can inspect failing GitHub Actions checks when enabled.
- R2: Fix workflows treat CI failures as repair constraints within the configured retry budget.
- R3: External setup or action-required failures are classified as blockers instead of normal code failures.
- R4: Cleanup steps preserve passing tests and do not hide unresolved CI failures.
- R5: The final PR evidence states whether CI passed, was skipped, or remains blocked.

## Context

CI validation closes the loop between local repair and repository-level safety.
For a regression suite similar to unit tests, CI failures need deterministic
classification and explicit status rather than optimistic success.

## Acceptance Criteria

1. Given CI validation is enabled and checks fail, when the fix workflow inspects CI, then it records the failing check names and relevant failure context.
2. Given the CI failure is actionable within the codebase, when retry budget remains, then the workflow attempts a bounded post-push repair.
3. Given the CI failure requires external setup or manual action, when classification runs, then the workflow reports a blocker instead of repeatedly patching unrelated code.
4. Given cleanup runs after repair, when it modifies files, then it does not remove passing tests or hide unresolved check failures.
5. Given CI is skipped by configuration, when the PR evidence is written, then the skip is explicit.

## Oracle

These details matter for pass/fail:
- CI failures are inspected when enabled
- retry budget controls post-push repair attempts
- action-required setup failures are blockers
- cleanup does not erase evidence
- final evidence distinguishes pass, skip, and blocked states

## Non-Oracle

These details should not matter:
- exact GitHub Actions log formatting
- exact provider/model used during a repair attempt
- cosmetic PR body wording
- exact retry backoff timing

## Negative Cases

- A locally passing fix must not be marked complete while enabled CI is failing.
- External setup failures must not trigger endless code patch attempts.
- Cleanup must not delete tests that captured the bug.
- Skipped CI must not be reported as passed CI.

## Non-Goals

- This story does not require live CI in local deterministic verification.
- This story does not prescribe every CI provider.
- This story does not merge anything into `main`.

## Candidate Prompts

- `prompts/ci_validation_python.prompt` - owns CI result inspection and classification.
- `prompts/agentic_e2e_fix_orchestrator_python.prompt` - owns the E2E fix loop.
- `prompts/agentic_e2e_fix_step10_ci_validation_LLM.prompt` - owns CI validation step behavior.
- `prompts/agentic_e2e_fix_step11_code_cleanup_LLM.prompt` - owns post-repair cleanup.
- `prompts/commands/fix_python.prompt` - owns the public `pdd fix` command surface.

## Notes

This story protects post-push validation as part of the same regression evidence
chain as local tests.
