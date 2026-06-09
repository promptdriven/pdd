<!-- pdd-story-contract derived-from-story="../story__pdd_bug.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd bug

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_bug.md`), not this contract.

## Covers

- R1: Bug command routes GitHub issue URLs to the agentic bug workflow.
- R2: Manual bug repair remains available for explicit prompt/code/program/output artifacts.
- R3: Mode-specific options are validated before execution.

## Context

The `pdd bug` command is implemented by `prompts/commands/analysis_python.prompt`,
which also owns other analysis commands. This contract covers only the `bug`
CLI surface.

## Acceptance Criteria

1. Given a GitHub issue URL, when the user runs `pdd bug <issue-url>`, then the command dispatches to the agentic bug workflow with the current verbosity, quiet, timeout, GitHub-state, and clean-restart choices.
2. Given `--manual` and the required prompt, code, program, current-output, and desired-output files, when the user runs `pdd bug`, then the command dispatches to the manual bug repair path.
3. Given `--clean-restart` outside agentic GitHub issue mode, when the user runs `pdd bug`, then the command rejects the invocation instead of silently ignoring or misrouting the flag.
4. Given a runtime failure from the underlying workflow, when the command handles it, then Click usage/abort exceptions preserve Click semantics and non-Click exceptions are reported through the standard command error handler.

## Oracle

These details matter for pass/fail:
- selected workflow: agentic bug vs manual bug repair
- required manual argument count
- validation of GitHub issue URL shape for agentic-only options
- forwarded quiet, verbose, timeout, GitHub-state, and clean-restart values
- Click exception propagation for usage and abort conditions

## Non-Oracle

These details should not matter:
- exact helper names used inside the command module
- exact color/style of console output
- exact wording of non-user-facing diagnostics
- which model/provider is selected downstream

## Negative Cases

- A normal web URL or non-issue GitHub URL must not be accepted as an agentic bug issue.
- `--clean-restart` must not be accepted in manual mode.
- Manual mode must not proceed with missing or misordered required artifacts.
- The command must not call both agentic and manual workflows for one invocation.

## Non-Goals

- This story does not cover `detect`, `conflicts`, `crash`, or `trace`.
- This story does not verify the internals of the agentic bug solver.
- This story does not prescribe exact LLM prompts or generated patch content.

## Candidate Prompts

- `prompts/commands/analysis_python.prompt` — primary owner of the `pdd bug` CLI.
- `prompts/agentic_bug_python.prompt` — related downstream agentic workflow.
- `prompts/bug_main_python.prompt` — related manual bug repair workflow.

## Notes

This story is part of the user-story coverage split requested from the PR 1501
integration comment so each command can be reviewed independently.

