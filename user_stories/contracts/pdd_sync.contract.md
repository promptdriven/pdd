<!-- pdd-story-contract derived-from-story="../story__pdd_sync.md" story-hash="db8793f0c80a101b" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd sync

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_sync.md`), not this contract.

## Covers

- R1: No-argument sync runs project-wide/global synchronization.
- R2: Basename sync runs single-module synchronization.
- R3: GitHub issue URLs run agentic issue synchronization.
- R4: Durable, snapshot, compression, budget, and steering options are routed only where supported.

## Context

The `pdd sync` command is implemented by
`prompts/commands/maintenance_python.prompt`, which also owns related
maintenance commands. This contract covers only the `sync` CLI surface.

## Acceptance Criteria

1. Given no basename, when the user runs `pdd sync`, then the command dispatches to project-wide global sync with resolved default budget, target coverage, one-session default, compression, steering, and local/model settings.
2. Given a non-URL basename, when the user runs `pdd sync <basename>`, then the command dispatches to single-module `sync_main` with the requested verification, test, snapshot, compression, steering, coverage, budget, and agentic options.
3. Given a GitHub issue URL, when the user runs `pdd sync <issue-url>`, then the command dispatches to agentic issue sync and forwards dry-run, one-session, durable, GitHub-state, timeout, compression, model-context, and reasoning-time settings.
4. Given durable options without an issue URL or without `--durable`, when the user invokes sync, then the command rejects the invalid durable option combination before running a workflow.
5. Given `--model`, when the command starts, then the model override is visible to downstream model selection for this invocation.
6. Given a failed sync result, when the command finishes, then it exits non-zero and prints status, message, cost, and a non-empty model when applicable.

## Oracle

These details matter for pass/fail:
- dispatch key: omitted basename vs GitHub issue URL vs normal basename
- default budget and target coverage resolution from `.pddrc`
- one-session contextual defaults by mode
- durable option validation and forwarding
- snapshot/compressed-context unsupported-path rejection instead of silent ignore
- `--no-github-state` forwarded as `use_github_state=False`

## Non-Oracle

These details should not matter:
- exact order of files synchronized downstream
- exact generated code/test/example content
- exact console color/style
- provider/model choice except explicit override propagation

## Negative Cases

- Durable sync options must not be accepted for no-argument or single-module sync.
- Durable companion flags must not be accepted without `--durable`.
- `architecture.json` must not be treated as a global-sync alias when passed as a positional basename.
- Unsupported snapshot/compressed-context requests must not be silently ignored.

## Non-Goals

- This story does not cover `sync-architecture`, `auto-deps`, or `setup`.
- This story does not verify all internals of `sync_main` or agentic sync.
- This story does not prescribe generated artifact content.

## Candidate Prompts

- `prompts/commands/maintenance_python.prompt` — primary owner of the `pdd sync` CLI.
- `prompts/sync_main_python.prompt` — related single-module sync workflow.
- `prompts/agentic_sync_python.prompt` — related global and issue sync workflows.
- `prompts/sync_orchestration_python.prompt` — related orchestration support.

## Notes

This story is part of the command-by-command user-story split requested from
the PR 1501 integration comment.
