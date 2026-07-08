<!-- pdd-story-contract derived-from-story="../story__pdd_context_compression_manifest.md" story-hash="aed7d941a928e1b1" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Context compression leaves an audit trail

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_context_compression_manifest.md`), not this contract.

## Covers

- R1: Context compression can select example, contract, and test context under a configured token budget.
- R2: Failing tests are prioritized before lower-signal tests.
- R3: Pytest slicing preserves the failing test and required fixtures when a file is too large.
- R4: The TestPackingManifest lists selected and omitted tests with reasons.
- R5: Compression fallback behavior is explicit when parsing, slicing, or ranking fails.

## Context

Context compression is useful only if it behaves like a reviewed, deterministic
test-selection system. This story covers selection, slicing, manifest output,
and explicit fallback reporting.

## Acceptance Criteria

1. Given test context compression is enabled and failing tests are known, when context is packed, then failing tests are selected first.
2. Given a test file is too large, when slicing is possible, then the selected context includes the failing test and required fixtures rather than the whole file.
3. Given the token budget is exhausted, when remaining tests are omitted, then the manifest explains the omission.
4. Given near-duplicate tests are found, when deduplication runs, then the manifest records which test was kept and which was omitted.
5. Given slicing or parsing fails, when fallback runs, then the fallback mode is visible instead of silently changing context.

## Oracle

These details matter for pass/fail:
- failing tests are prioritized
- selected and omitted context is explained
- sliced tests keep required fixtures
- fallback behavior is explicit
- compressed context still reports the behavioral evidence sent to the model

## Non-Oracle

These details should not matter:
- exact ranking score decimals
- exact token-count library internals
- cosmetic manifest formatting
- unrelated provider/model choice

## Negative Cases

- A failing test must not be omitted merely because a lower-signal test was ranked first.
- The manifest must not hide omitted tests.
- A slicing failure must not silently drop all test context.
- Compression must not mutate source tests.

## Non-Goals

- This story does not prescribe the final ranking formula weights.
- This story does not require live model calls.
- This story does not cover every possible test framework.

## Candidate Prompts

- `prompts/content_selector_python.prompt` - owns context selection.
- `prompts/test_context_packer_python.prompt` - owns test context packing and manifests.
- `prompts/pytest_slicer_python.prompt` - owns pytest slicing.
- `prompts/llm_invoke_python.prompt` - carries packed context into model invocation.

## Notes

This story protects context compression as a transparent, unit-test-like
selection step instead of an invisible cost optimization.
