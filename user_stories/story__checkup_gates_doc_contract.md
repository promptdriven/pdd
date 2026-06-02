<!-- pdd-story-prompts: pdd/prompts/agentic_change_orchestrator_python.prompt, pdd/prompts/agentic_common_python.prompt, pdd/prompts/checkup_gates_python.prompt, pdd/prompts/commands/checkup_python.prompt, pdd/prompts/commands/gate_python.prompt, pdd/prompts/context_generator_main_python.prompt, pdd/prompts/core/cli_python.prompt, pdd/prompts/evidence_manifest_python.prompt, pdd/prompts/evidence_store_python.prompt, pdd/prompts/fix_error_loop_python.prompt, pdd/prompts/fix_focus_python.prompt, pdd/prompts/fix_main_python.prompt, pdd/prompts/gate_policy_python.prompt, pdd/prompts/gate_python.prompt, pdd/prompts/generate_model_catalog_python.prompt, pdd/prompts/grounding_policy_python.prompt, pdd/prompts/llm_invoke_python.prompt, pdd/prompts/llm_model_csv.prompt, pdd/prompts/operation_log_python.prompt, pdd/prompts/sync_orchestration_python.prompt -->

# User Story: Doc Contract Gate Coverage

## Covers

- R1: Deterministic review-loop gates must block clean verdicts when user-facing contracts are undocumented.

## Story

As a maintainer reviewing prompt and documentation changes,
I want the doc-contract gate to catch undocumented user-facing surfaces and missing prompt story coverage,
so that prompt changes stay testable through `pdd detect --stories`.

## Context

This story covers the doc-contract behavior specified by `pdd/prompts/checkup_gates_python.prompt` and links the prompt files changed in this PR so `pdd detect --stories` has an explicit prompt-regression scope.

## Acceptance Criteria

1. Given a PR adds a user-facing surface, when the doc-contract gate runs, then the gate requires the configured documentation to mention that surface.
2. Given a PR changes a non-LLM `.prompt` file, when the doc-contract gate runs, then at least one `user_stories/story__*.md` file links that prompt through `pdd-story-prompts` metadata or an explicit prompt reference.
3. Given `pdd detect --stories` is run, when this story is analyzed against `pdd/prompts/checkup_gates_python.prompt`, then it reports no required prompt changes.

## Oracle

These details matter for pass/fail:
- Doc-contract failures name the missing documentation or story coverage.
- Story coverage accepts full prompt paths, basenames, and paths relative to a `prompts/` segment.
- The deterministic gate enforces the existence of a story-test artifact without running the LLM-backed story suite itself.

## Non-Oracle

These details should not matter:
- Private helper names in `pdd/checkup_gates.py`.
- Exact ordering of unrelated deterministic gates.
- Exact wording of successful gate output.

## Negative Cases

- A prompt change without any linked story must fail the doc-contract gate.
- A story that links an unrelated prompt must not satisfy coverage for the changed prompt.

## Non-Goals

This story does not require `doc-contract` to execute `pdd detect --stories`; the executable story suite remains the responsibility of the story-test command and evidence gate.
