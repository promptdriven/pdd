<!-- pdd-story-contract derived-from-story="../story__pdd_story_test_coverage.md" story-hash="8fdc178d30078079" issue-ref="https://github.com/promptdriven/pdd/issues/1769" -->

# Contract: Story tests appear in coverage

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_story_test_coverage.md`), not this contract.

## Covers

- R1: `pdd test --issue <source> <prompt...>` creates or updates story artifacts linked to every supplied prompt.
- R2: Existing `story__*.md` files can refresh prompt-link metadata through story mode.
- R3: Story contracts retain rule coverage and candidate prompt context for reviewers.
- R4: `pdd checkup coverage` includes story evidence in the rule-to-evidence matrix.
- R5: Cross-dev-unit stories are attributed to each linked prompt while counted once globally.
- R6: Coverage output exposes unresolved, stale, or missing evidence without treating cross-unit metadata as separate stories.

## Context

The documented story-mode test workflow uses `pdd test` with prompt files or an
existing `story__*.md` file to generate or refresh user-story artifacts. Coverage
then reads story/contract evidence through `pdd checkup coverage`. This crosses
the generate/test command surface, agentic test workflow, story utility module,
coverage engine, and checkup delegation command.

## Acceptance Criteria

1. Given an issue source and two or more prompt files, when the user runs `pdd test --issue <source> <prompt...>`, then PDD writes a story linked to every supplied prompt.
2. Given an existing `story__*.md` file, when the user runs `pdd test <story-file>`, then PDD refreshes prompt-link metadata rather than treating the story as code input.
3. Given a story contract lists covered rules, when coverage scans the prompt, then the matching story appears as evidence for those rule IDs.
4. Given a story links multiple prompts, when coverage scans each prompt, then the story is attributed to each prompt without creating multiple global story identities.
5. Given evidence is stale, missing, or unresolved, when coverage renders output, then reviewers can see that status instead of receiving a silent pass.
6. Given the story lane summary groups by story slug, when this cross-unit story appears, then it is reported once with its linked dev-unit scope.

## Oracle

These details matter for pass/fail:
- story-mode routing in `pdd test`
- prompt metadata is written or refreshed for every linked prompt
- story contract rule coverage feeds the coverage matrix
- missing/stale evidence remains visible
- global metrics deduplicate by story identity
- cross-unit metadata lists every participating dev unit

## Non-Oracle

These details should not matter:
- exact LLM-authored story wording
- exact terminal table styling
- exact provider/model used for story generation
- exact order of unrelated coverage rows

## Negative Cases

- A story file must not be handled as a normal prompt/code unit-test input.
- A multi-prompt story must not be reported as separate unrelated stories.
- Missing or stale evidence must not be hidden by the cross-unit grouping.
- Coverage must not count this one cross-unit story once for each linked prompt.

## Non-Goals

- This story does not verify the generated executable test contents.
- This story does not cover live model availability.
- This story does not prescribe the exact coverage table formatting.

## Candidate Prompts

- `prompts/commands/generate_python.prompt` - owns the public `pdd test` command surface.
- `prompts/agentic_test_orchestrator_python.prompt` - owns issue-driven test workflow orchestration.
- `prompts/user_story_tests_python.prompt` - owns story metadata and traceability.
- `prompts/coverage_contracts_python.prompt` - owns deterministic rule-to-evidence coverage.
- `prompts/commands/checkup_python.prompt` - delegates `pdd checkup coverage`.
- `prompts/agentic_test_step6_coverage_LLM.prompt` - related test-plan coverage step.

## Notes

This story is a cross-dev-unit regression oracle for the documented
story-mode test workflow and issue #1769 coverage requirements.
