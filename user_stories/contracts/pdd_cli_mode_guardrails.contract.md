<!-- pdd-story-contract derived-from-story="../story__pdd_cli_mode_guardrails.md" story-hash="7aa444b31df66e23" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: CLI mode guardrails reject ambiguous requests

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_cli_mode_guardrails.md`), not this contract.

## Covers

- R1: Shared CLI parsing preserves Click usage errors and abort semantics.
- R2: Generate-mode guardrails reject mutually exclusive prompt/template, dry-run, estimate, and PRD options.
- R3: Modify-mode guardrails reject manual, issue-driven, CSV, change, and update combinations that cannot be routed safely.
- R4: Maintenance-mode guardrails reject sync options that are valid only for other sync modes.
- R5: A rejected request exits before any provider, file mutation, or GitHub workflow starts.

## Context

This is a unit-test-like CLI regression story for behavior that should be as
stable as ordinary Python argument-validation unit tests. It spans the shared
CLI entry point and the generate, modify, and maintenance command groups.

## Acceptance Criteria

1. Given mutually exclusive options, when the user invokes a PDD command, then PDD raises a usage error before downstream workflow code runs.
2. Given a generate request mixes prompt-file, template, PRD, and dry-run modes incompatibly, when parsing completes, then no files are written and no model call starts.
3. Given a modify request mixes issue-driven and manual/CSV modes incompatibly, when parsing completes, then no prompt or code file is changed.
4. Given a sync request uses durable, snapshot, or compression options on an unsupported sync path, when parsing completes, then PDD rejects the request instead of silently ignoring the option.
5. Given Click raises `UsageError`, `Abort`, or `Exit`, when the command wrapper handles it, then the original Click semantics are preserved.

## Oracle

These details matter for pass/fail:
- invalid option combinations are rejected before side effects
- Click usage and abort exceptions are not swallowed
- generated files, prompt files, and GitHub state remain untouched on parse failure
- mode-specific guardrails stay attached to the correct command families
- rejected requests report actionable command-line feedback

## Non-Oracle

These details should not matter:
- exact color or Rich formatting of the usage output
- exact helper names in the command modules
- provider/model defaults that would have been used after validation
- ordering of unrelated command options in help text

## Negative Cases

- A typo in mode flags must not silently fall through to a default workflow.
- An invalid generate request must not create output, evidence, or cost rows.
- An invalid modify request must not stage partial prompt/story artifacts.
- An invalid sync request must not ignore unsupported durability or context flags.

## Non-Goals

- This story does not verify generated code content.
- This story does not cover every option on every command.
- This story does not require live provider credentials.

## Candidate Prompts

- `prompts/core/cli_python.prompt` - owns shared CLI wiring and Click exception handling.
- `prompts/commands/generate_python.prompt` - owns generate and test mode guardrails.
- `prompts/commands/modify_python.prompt` - owns change and update mode guardrails.
- `prompts/commands/maintenance_python.prompt` - owns sync mode guardrails.

## Notes

This story protects unit-test-like CLI behavior: invalid inputs should fail
fast, locally, and without side effects.
