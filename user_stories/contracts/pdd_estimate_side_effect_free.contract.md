<!-- pdd-story-contract derived-from-story="../story__pdd_estimate_side_effect_free.md" story-hash="3fd5c07d4059d77b" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Estimate mode previews cost without changing files

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_estimate_side_effect_free.md`), not this contract.

## Covers

- R1: Global estimate mode routes supported standard generation requests to cost preview logic.
- R2: Estimate mode returns prompt/model/cost information without invoking a real generation.
- R3: Estimate mode does not write command outputs, evidence manifests, generated code, or cost rows.
- R4: Unsupported agentic or multi-step paths reject estimate mode instead of pretending to estimate them.
- R5: Normal generation remains unchanged when estimate mode is not requested.

## Context

Estimate mode should behave like a dry unit test for generation cost: it answers
"what would this cost?" without mutating repository state or provider state.

## Acceptance Criteria

1. Given a standard prompt-file generation request and global estimate mode, when the command runs, then it returns an estimate payload.
2. Given estimate mode is active, when the command completes, then no generated code, evidence manifest, or cost row is written.
3. Given a path uses agentic or multi-step generation, when estimate mode is requested and unsupported, then PDD rejects it clearly.
4. Given normal generation runs without estimate mode, when the command completes, then existing generation side effects remain available.
5. Given estimate mode inspects model selection, when reporting cost, then it does not require a real provider completion.

## Oracle

These details matter for pass/fail:
- supported standard generation can estimate
- unsupported paths reject estimate mode
- no generated outputs, evidence, or cost rows are written
- estimate reporting includes enough information for budgeting
- normal generation is unaffected

## Non-Oracle

These details should not matter:
- exact dollar amount for a future model catalog update
- cosmetic output formatting
- provider-specific implementation details
- exact internal helper names

## Negative Cases

- Estimate mode must not write generated code.
- Estimate mode must not append a real run cost row.
- Unsupported multi-step workflows must not return a misleading estimate.
- Normal generation must not be accidentally converted into estimate behavior.

## Non-Goals

- This story does not guarantee exact billing for future provider pricing changes.
- This story does not cover hosted billing dashboards.
- This story does not require live model credentials.

## Candidate Prompts

- `prompts/commands/generate_python.prompt` - owns generate command estimate routing.
- `prompts/code_generator_main_python.prompt` - owns standard prompt-file generation.
- `prompts/track_cost_python.prompt` - owns cost accounting behavior.
- `prompts/llm_invoke_python.prompt` - owns model invocation boundaries.

## Notes

This story protects estimate mode as a side-effect-free budgeting regression.
