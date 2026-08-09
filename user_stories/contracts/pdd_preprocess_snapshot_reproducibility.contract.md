<!-- pdd-story-contract derived-from-story="../story__pdd_preprocess_snapshot_reproducibility.md" story-hash="5bc489a56ca311f6" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Preprocessed prompts can be replayed

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_preprocess_snapshot_reproducibility.md`), not this contract.

## Covers

- R1: Preprocess expands includes, shell/web directives, and template variables into the prompt sent to the model.
- R2: Missing includes or unsafe dynamic directives fail with actionable diagnostics before generation.
- R3: Snapshot mode records replayable evidence for dynamic context that affects contract-critical prompts.
- R4: Context inspection reports hydrated token counts without triggering generation.
- R5: Replay and audit metadata make it possible to inspect what the model saw later.

## Context

Preprocess and snapshot behavior is a unit-test-like foundation for all PDD
generation: if prompt hydration is unstable, every higher-level story can rot.
This story spans preprocess expansion, the preprocess CLI, snapshot capture, and
context inspection.

## Acceptance Criteria

1. Given a prompt with static includes, when preprocess runs, then the included content appears in the hydrated prompt in the documented location.
2. Given a prompt references a missing include, when preprocess runs, then it fails clearly before any model call.
3. Given a prompt uses dynamic shell or web context under snapshot mode, when preprocess completes, then replayable snapshot evidence records the expanded input.
4. Given `pdd context <prompt>` is used for inspection, when it reports token counts, then it does not start a generation workflow.
5. Given reviewers inspect a generated artifact later, when snapshot evidence exists, then they can identify the prompt context that shaped the output.

## Oracle

These details matter for pass/fail:
- include expansion is deterministic
- missing context fails before generation
- dynamic context can be snapshotted and replayed
- context inspection remains read-only
- hydrated prompt evidence is available for audit

## Non-Oracle

These details should not matter:
- exact model provider configuration
- exact token count implementation as long as counts are stable enough for budgeting
- cosmetic formatting of context reports
- unrelated prompt rewrite behavior

## Negative Cases

- Missing include files must not be silently omitted.
- Dynamic contract-critical context must not be used without replayable evidence when snapshot mode is required.
- Context inspection must not write generated code or cost rows.
- Snapshot evidence must not point at an unrelated prompt.

## Non-Goals

- This story does not require live network access.
- This story does not prescribe every supported directive.
- This story does not verify model output quality.

## Candidate Prompts

- `prompts/preprocess_python.prompt` - owns prompt directive expansion.
- `prompts/preprocess_main_python.prompt` - owns preprocess command behavior.
- `prompts/context_snapshot_python.prompt` - owns replayable dynamic context snapshots.
- `prompts/commands/context_python.prompt` - owns context inspection commands.

## Notes

This story makes prompt hydration itself part of the regression suite.
