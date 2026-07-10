<!-- pdd-story-contract derived-from-story="../story__pdd_change.md" story-hash="3d3e24afdcf4ac7e" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd change

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_change.md`), not this contract.

## Covers

- R1: GitHub issue URLs route to agentic change.
- R2: Manual change requests still support file and CSV workflows.
- R3: Generated user story artifacts are staged with the change.
- R4: The generated contract sidecar travels alongside the human story.

## Context

The `pdd change` command is implemented by
`prompts/commands/modify_python.prompt`. PR 1501's integration comment notes
that the parent branch wires the agentic-change hook to stage
`user_stories/contracts/<slug>.contract.md` alongside the human story.

## Acceptance Criteria

1. Given one GitHub issue URL and no manual override, when the user runs `pdd change <issue-url>`, then the command invokes agentic change with GitHub-state, clean-restart, timeout, budget, and verbosity choices.
2. Given `--manual` with a standard change file, code file, and prompt file, when the user runs `pdd change`, then the command invokes the manual change path after validating all required files.
3. Given `--manual --csv` with a change file and code directory, when the user runs `pdd change`, then the command invokes CSV/manual change mode and validates that the code input is a directory.
4. Given agentic change generates a human story, when the command stages generated artifacts for the change PR, then it stages both `user_stories/story__<slug>.md` and the sibling `user_stories/contracts/<slug>.contract.md`.
5. Given story generation fails during agentic change, when the main change workflow succeeds, then the command reports the story failure as non-blocking rather than failing the whole change.
6. Given `--clean-restart` outside agentic GitHub issue mode, when the user invokes the command, then the command rejects the request before running a workflow.

## Oracle

These details matter for pass/fail:
- agentic vs manual vs CSV routing
- file-vs-directory validation for manual modes
- environment restoration for GitHub-state suppression
- staging of both story and contract paths when generated
- non-blocking story-generation failure behavior
- failed workflow exits non-zero

## Non-Oracle

These details should not matter:
- exact PR body prose beyond including story summary when available
- exact story slug chosen by the LLM, as long as linked files are staged together
- exact console styling
- exact downstream prompt patch content

## Negative Cases

- The contract sidecar must not be left unstaged when the human story is staged.
- Manual CSV mode must not accept a regular code file where a directory is required.
- `--clean-restart` must not be accepted with manual mode or non-issue URLs.
- Story generation failure must not hide the main change result.

## Non-Goals

- This story does not cover `pdd split` or `pdd update`.
- This story does not verify story text quality beyond artifact presence/linkage.
- This story does not prescribe the agentic change internal step sequence.

## Candidate Prompts

- `prompts/commands/modify_python.prompt` — primary owner of the `pdd change` CLI.
- `prompts/agentic_change_python.prompt` — related agentic change workflow.
- `prompts/change_main_python.prompt` — related manual change workflow.
- `prompts/generate_user_story_LLM.prompt` — related human story generation.
- `prompts/generate_story_contract_LLM.prompt` — related contract sidecar generation.

## Notes

This story directly reflects the PR 1501 integration comment: the parent branch
must stage the generated contract sidecar alongside the human story so both
travel with the change PR.
