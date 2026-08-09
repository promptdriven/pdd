<!-- pdd-story-contract derived-from-story="../story__pdd_checkup.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd checkup

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_checkup.md`), not this contract.

## Covers

- R1: Local utility targets dispatch before agentic issue/PR validation.
- R2: Prompt-shaped targets run deterministic prompt checkup.
- R3: Issue and PR targets run the appropriate agentic checkup workflow.
- R4: Mutually exclusive options fail early with useful Click errors.

## Context

The `pdd checkup` command is implemented by
`prompts/commands/checkup_python.prompt`. It intentionally keeps a single
top-level command while dispatching to lint, contract, coverage, gate,
simplify, prompt-target, issue, PR, review-loop, and final-gate modes.

## Acceptance Criteria

1. Given a reserved local utility target such as `lint`, `contract`, `contracts`, `coverage`, `gate`, or `simplify`, when the user runs `pdd checkup <target>`, then the command forwards to that utility without requiring a GitHub issue URL.
2. Given a prompt-shaped local target, when the user runs `pdd checkup <prompt-target>`, then the command runs prompt source-set checkup and optional prompt repair instead of agentic issue checkup.
3. Given a GitHub issue URL target, when the user runs `pdd checkup <issue-url>`, then the command invokes the agentic issue checkup workflow with the requested fix, state, timeout, start-step, prompt-repair, and test-scope settings.
4. Given `--pr`, when the user runs PR-mode checkup, then the command verifies the PR URL, treats `--issue` as optional except where review-loop/final-gate requires it, and forwards the effective PR/issue context.
5. Given final-gate or review-loop option conflicts, when the user invokes the command, then the command rejects the invocation before running an LLM or mutating a PR.
6. Given a failed checkup result, when the command finishes, then it exits non-zero and reports the status, message, cost, and non-empty model when appropriate.

## Oracle

These details matter for pass/fail:
- dispatch order: local utility, prompt target, validation mode, PR mode, issue mode
- URL shape validation for issues and PRs
- mutually exclusive flag behavior for final-gate and review-loop
- forwarding of prompt-repair, review-loop, gate, and GitHub-state options
- JSON/machine-output invocations remain parseable when applicable
- non-zero exit on failed verdicts

## Non-Oracle

These details should not matter:
- exact LLM reviewer/fixer wording
- exact order of unrelated option declarations in help output
- internal helper names
- cosmetic formatting of human-readable summaries

## Negative Cases

- `--issue` without `--pr` must be rejected.
- `--review-loop` must not run without both PR and issue context.
- `--final-gate` must not combine with review-only, no-fix, no-gates, or start-step overrides.
- Local utility targets must not be misclassified as GitHub issue targets.
- Prompt-target checkup must not call the agentic issue orchestrator.

## Non-Goals

- This story does not assert every individual reviewer-loop finding format.
- This story does not verify downstream repair implementations.
- This story does not cover `pdd checkup simplify` internals beyond dispatch.

## Candidate Prompts

- `prompts/commands/checkup_python.prompt` — primary owner of the `pdd checkup` CLI.
- `prompts/agentic_checkup_python.prompt` — related agentic issue/PR workflow.
- `prompts/commands/checkup_simplify_python.prompt` — related simplify sub-dispatch.
- `prompts/commands/contracts_python.prompt` — related contract utility dispatch.
- `prompts/commands/gate_python.prompt` — related deterministic gate utility dispatch.

## Notes

This story is part of the command-by-command user-story split requested from
the PR 1501 integration comment.
