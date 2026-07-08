<!-- pdd-story-contract derived-from-story="../story__agentic_sync_runner_code_generator_main.md" story-hash="0bc19a2ead30fc6b" issue-ref="https://github.com/promptdriven/pdd/issues/1649" -->

# Contract: Classify prose/empty LLM generation output separately from architecture regressions

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__agentic_sync_runner_code_generator_main.md`), not this contract.

## Covers
- AC1: A provider response containing only prose/planning text is reported as a generation-output/extraction failure, not as a missing-symbol architecture failure.
- AC2: The target file is not overwritten when the model returns no extractable code.
- AC3: The diagnostic includes enough context (raw-output excerpt, provider/model, prompt name, output path, extractor result) to debug the output-shape problem.
- R1: The error type is distinct from architecture-conformance errors (e.g., `GenerationOutputExtractionError` or `EmptyGenerationError`).

## Context
- A `pdd generate` or `pdd sync` run targets a code-generation prompt (e.g., `code_generator_main_python.prompt` or `agentic_sync_runner_python.prompt`).
- The underlying LLM provider returns a response that contains only natural-language planning text, an agentic-style reasoning sentence, or is empty — with no extractable source-code block.
- The extractor correctly returns no code (empty string or equivalent).
- The existing architecture-conformance gate and empty-overwrite guard remain in place as backstops.

## Acceptance Criteria
1. Given a code-generation prompt and a mocked provider response that contains only prose (e.g., “First I’ll look for an existing implementation…”), when the generation pipeline processes the response, then the pipeline raises a distinct generation-output/extraction error before reaching the architecture-conformance gate.
2. Given the distinct generation-output/extraction error is raised, when the error is reported, then the diagnostic message includes the raw-output excerpt, provider/model name, prompt name, output path, and extractor result.
3. Given the distinct generation-output/extraction error is raised, when the pipeline handles the failure, then the target output file is not overwritten.
4. Given the distinct generation-output/extraction error is raised and a retry is attempted, when the retry directive is constructed, then it asks for complete source code rather than only listing missing symbols.

## Oracle
These details matter for pass/fail:
- A prose-only or empty provider response triggers an error whose type is distinct from the architecture-conformance missing-symbol error.
- The error is raised before the architecture-conformance check runs.
- The error diagnostic payload contains: a raw-output excerpt, the provider/model identifier, the prompt name, the output path, and the extractor result.
- The target file on disk is unchanged after the error.
- If a retry is issued, the retry prompt includes a directive to return the complete source file only, not a plan.

## Non-Oracle
These details should not matter:
- The exact class name of the new error (e.g., `GenerationOutputExtractionError` vs `EmptyGenerationError`).
- The exact wording of the diagnostic message, as long as the required fields are present.
- Whether the check lives in `code_generator_main`, the extractor layer, a local provider adapter, or sync retry handling.
- The specific LLM provider or model that produced the prose response.
- The exact retry mechanism (immediate retry, deferred retry, manual retry).

## Negative Cases
- A prose-only or empty provider response is reported as a standard architecture-conformance missing-symbol error.
- The target file is overwritten with empty or non-code content when the model returns no extractable code.
- The error diagnostic omits the raw-output excerpt, provider/model, prompt name, output path, or extractor result.
- A retry directive asks only for missing symbols without addressing the output-shape problem.

## Non-Goals
- Fixing provider responses that are not code at all (this story only covers detection and distinct reporting).
- Changing the architecture-conformance gate or empty-overwrite guard behavior for responses that do contain extractable code.
- Addressing compatibility-surface contracts or model-guidance improvements (separate from #1647).

## Candidate Prompts
- `agentic_sync_runner_python.prompt` — (primary) Directly invoked during sync runs that can encounter prose-only LLM responses.
- `code_generator_main_python.prompt` — (primary) Core code generation path where prose-only responses must be detected before architecture checks.
- `agentic_bug_orchestrator_python.prompt` — (related) Orchestrates generate attempts and would benefit from distinct extraction-failure signaling.
- `agentic_change_orchestrator_python.prompt` — (related) Same generate-attempt pattern; prose responses would confuse its repair loop.
- `agentic_architecture_orchestrator_python.prompt` — (related) Multi-step architecture workflow that invokes generation and needs clear failure classification.
- `agentic_e2e_fix_orchestrator_python.prompt` — (related) Orchestrates generate steps where prose-only output would mislead the fix loop.
- `agentic_test_orchestrator_python.prompt` — (related) 18-step test generation workflow that calls code generation and needs distinct extraction errors.
- `agentic_sync_python.prompt` — (related) Global sync orchestration that dispatches to runners and would propagate distinct error types.
- `agentic_fix_python.prompt` — (possible) High-level orchestration that may encounter generation failures during fix workflows.
- `agentic_split_orchestrator_python.prompt` — (possible) Diagnoses and splits dev units; may invoke generation where prose responses need distinct handling.

## Notes
- This story originated from investigation of #1641 / PR #1644 where a local ChatGPT/Codex-style provider returned a planning sentence instead of code.
- The existing architecture-conformance and empty-overwrite guards remain as backstops; this contract adds an earlier, more precise classification gate.
- The issue explicitly states this is separate from #1647 (compatibility-surface contracts).
- The sync owner decides the exact placement of the check (generator, extractor, provider adapter, or retry handler); the contract asserts only the observable behavior.
