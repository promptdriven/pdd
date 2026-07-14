<!-- pdd-story-prompts: agentic_arch_step13_fix_LLM.prompt -->

# User Story: Architecture validation repairs preserve repository layout

## Story

As a maintainer repairing a failed architecture validation step, I want the repair agent to change only evidence-linked artifacts and preserve the repository's declared prompt layout, so a repair cannot erase nested prompts or move unrelated files.

## Covers

- R1: Repairs write only artifacts that directly cause the reported validation failure.
- R2: Nested prompt paths and architecture filenames follow the selected `.pddrc` strategy.
- R3: Files and metadata remain in place unless repository evidence identifies them as stale or misplaced.
- R4: Every edit receives deterministic validation and an explicit result report.

## Context / Fixtures

The deterministic regression reads the shipped step-13 repair prompt and exercises the Issue #617 filepath-to-prompt normalization used by architecture synchronization. No external service or model call is required.

## Acceptance Criteria

1. Given diagnostics that identify one artifact, when the repair instructions execute, then they write only that artifact or another file whose path or content appears in those diagnostics.
2. Given Strategy B or a nested `.pddrc` `prompts_dir`, when architecture filenames are repaired, then the instructions preserve the nested prompt and write a filename that mirrors the code filepath directory.
3. Given a file that repository evidence does not identify as stale or misplaced, when the repair instructions execute, then they leave the file at its current path and do not delete it.
4. Given one or more edited artifacts, when validation finishes, then the result outputs `FILES_MODIFIED`, `FILES_DELETED`, and the deterministic validation results.

## Oracle

- The repair prompt contains the bounded-write, nested-layout, deletion, and validation-report contracts.
- Architecture normalization maps nested code filepaths to path-mirroring prompt filenames.

## Non-Oracle

- Model wording outside the four contracts.
- The order of independent validation commands.
- Formatting of diagnostic prose outside the required result fields.

## Forbidden Outcomes

- Blanket deletion of nested prompts in a Strategy B repository.
- Flattening a nested architecture filename into an underscore-only basename.
- Moving an unrelated file because it appears near a reported artifact.
- Reporting completion without deterministic validation results.
