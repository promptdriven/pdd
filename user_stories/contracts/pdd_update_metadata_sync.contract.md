<!-- pdd-story-contract derived-from-story="../story__pdd_update_metadata_sync.md" story-hash="e8f082eb49aef36a" issue-ref="https://github.com/promptdriven/pdd/issues/1769" -->

# Contract: Code changes update the prompt source

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_update_metadata_sync.md`), not this contract.

## Covers

- R1: `pdd update` routes repository-wide and file-specific update modes without ambiguous option combinations.
- R2: Accepted code behavior is back-propagated into the prompt source of truth.
- R3: Agentic update is used where available and legacy update paths remain explicit fallbacks.
- R4: Metadata synchronization runs when requested and can fail the command if required metadata cannot be refreshed.
- R5: Successful updates clear stale run reports and finalize prompt/code fingerprints.
- R6: The cross-dev-unit story is attributed to modify command, update engine, agentic update, metadata sync, and operation logging without duplicate global counting.

## Context

The documented update workflow asks maintainers to decide when implementation
knowledge belongs in the prompt. `pdd update` back-propagates accepted code
behavior into prompt files, and metadata/fingerprint finalization keeps the
prompt-code state auditable. This crosses the modify command surface, update
engine, agentic update path, metadata synchronization, and operation log.

## Acceptance Criteria

1. Given a repository-wide or file-specific update request, when the user runs `pdd update`, then PDD validates the selected mode before running update logic.
2. Given a code change reflects accepted behavior, when update succeeds, then the corresponding prompt is updated rather than leaving the accepted behavior only in generated code.
3. Given agentic update is available, when the update path uses it, then legacy fallback remains explicit and does not hide failures.
4. Given `--sync-metadata` is requested, when metadata synchronization fails, then the update command reports failure rather than silently succeeding.
5. Given an update succeeds without redirected output, when finalization runs, then stale run reports are cleared and a fresh prompt/code fingerprint is recorded.
6. Given coverage reports this story, when update and metadata dev units are listed separately, then this story appears under each linked unit but is counted once globally.

## Oracle

These details matter for pass/fail:
- update-mode validation before work starts
- accepted code behavior is copied back to prompts
- agentic and fallback update paths are distinguishable
- metadata synchronization failure is surfaced
- stale run-report cleanup and fingerprint finalization happen after successful update
- cross-unit metadata lists every participating dev unit

## Non-Oracle

These details should not matter:
- exact prompt prose produced by the updater
- exact provider/model selected
- exact progress table styling
- exact ordering of unrelated repository-mode candidates

## Negative Cases

- Ambiguous update modes must not proceed to prompt modification.
- Accepted behavior must not remain only in generated code after a successful update.
- Metadata synchronization failure must not be swallowed as success.
- Coverage must not count this one cross-unit story once for each linked prompt.

## Non-Goals

- This story does not verify semantic correctness of every generated prompt edit.
- This story does not cover `pdd change` feature workflow.
- This story does not require live model calls in deterministic local verification.

## Candidate Prompts

- `prompts/commands/modify_python.prompt` - owns the public `pdd update` command surface.
- `prompts/update_main_python.prompt` - owns update routing and prompt back-propagation.
- `prompts/agentic_update_python.prompt` - owns agentic update behavior.
- `prompts/metadata_sync_python.prompt` - owns metadata synchronization.
- `prompts/operation_log_python.prompt` - owns fingerprint and run-report metadata.
- `prompts/detect_change_main_python.prompt` - related change detection support.

## Notes

This story is a cross-dev-unit regression oracle for the documented
code-to-prompt update workflow in `docs/prompting_guide.md`.
