<!-- pdd-story-contract derived-from-story="../story__pdd_test.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd test

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_test.md`), not this contract.

## Covers

- R1: GitHub issue URLs route to agentic test generation.
- R2: Manual prompt/code inputs route to unit-test generation.
- R3: Issue-backed prompt inputs generate reviewable user story artifacts.
- R4: Existing story files can refresh prompt-link metadata.

## Context

The `pdd test` command is implemented by
`prompts/commands/generate_python.prompt`, which owns the generate suite. This
contract covers only the `test` command surface.

## Acceptance Criteria

1. Given a GitHub issue URL and no manual override, when the user runs `pdd test <issue-url>`, then the command invokes agentic test mode and forwards timeout, GitHub-state, clean-restart, and global model settings.
2. Given `--manual` or legacy prompt/code inputs, when the user runs `pdd test <prompt> <code>`, then the command invokes manual unit-test generation with output, language, coverage, merge, and existing-test settings.
3. Given `--issue <source>` and one or more `.prompt` files, when the user runs `pdd test --issue <source> <prompt...>`, then the command generates a human-reviewable user story from the issue text while linking the prompt files as validation targets.
4. Given a Markdown file named `story__*.md`, when the user runs `pdd test <story-file>`, then the command refreshes cached prompt-link metadata for that existing story rather than generating unit tests.
5. Given an invalid issue source or invalid LLM story output in story generation mode, when the command runs, then it hard-fails with a clear error and does not fall back to prompt-authored deterministic story text.
6. Given `--clean-restart` outside agentic GitHub issue mode, when the user invokes the command, then the command rejects the request before running any workflow.

## Oracle

These details matter for pass/fail:
- routing among agentic issue, story generation, story linking, and manual unit-test modes
- issue source is required for story generation mode
- prompt file paths are linked as metadata and not exposed as the story author's source text
- generated story path and linked prompts are surfaced to the user
- `@log_operation(operation="test", updates_run_report=True)` semantics remain attached
- Click usage errors are re-raised, not swallowed

## Non-Oracle

These details should not matter:
- exact generated test code
- exact LLM-authored story wording as long as it passes validation
- exact console style
- exact downstream model/provider used

## Negative Cases

- A story file must not be treated as a prompt file for manual unit-test generation.
- Story generation must not proceed without a resolvable issue source.
- Story generation must not include prompt file content in the authoring context.
- Non-issue URLs must not be accepted for agentic test clean-restart mode.

## Non-Goals

- This story does not cover `pdd generate` or `pdd example`.
- This story does not assert the full quality of generated tests.
- This story does not verify the internals of `run_agentic_test`.

## Candidate Prompts

- `prompts/commands/generate_python.prompt` — primary owner of the `pdd test` CLI.
- `prompts/agentic_test_python.prompt` — related agentic issue testing workflow.
- `prompts/cmd_test_main_python.prompt` — related manual unit-test generation workflow.
- `prompts/user_story_tests_python.prompt` — related story generation/linking support.

## Notes

This story is part of the command-by-command user-story split requested from
the PR 1501 integration comment.
