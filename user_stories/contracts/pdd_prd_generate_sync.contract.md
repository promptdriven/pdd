<!-- pdd-story-contract derived-from-story="../story__pdd_prd_generate_sync.md" story-hash="50dfcb910ae19ae4" issue-ref="https://github.com/promptdriven/pdd/issues/1769" -->

# Contract: PRD generate output can be synced into a module

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_prd_generate_sync.md`), not this contract.

## Covers

- R1: A GitHub issue or PRD source routes `pdd generate` to the architecture workflow.
- R2: The architecture workflow produces reviewable project configuration and prompt files.
- R3: Generated prompt files remain valid inputs to `pdd sync <module>`.
- R4: Sync preserves the selected module boundary instead of treating the PRD as a global rewrite.
- R5: The handoff records enough evidence for reviewers to connect the synced module back to the original request.
- R6: The cross-dev-unit story is attributed to generate, architecture, sync, and maintenance command prompts without being counted as four stories.

## Context

The documented PRD workflow says `pdd generate <issue-url>` creates
`architecture.json`, `.pddrc`, and prompt files, then the user can run
`pdd sync my_module` on generated prompts. This crosses the generate command,
agentic architecture workflow, sync implementation, and maintenance command
surface.

## Acceptance Criteria

1. Given a GitHub issue containing a PRD, when the user runs `pdd generate <issue-url>`, then PDD routes to the architecture workflow rather than ordinary single-prompt generation.
2. Given the architecture workflow succeeds, when the user reviews the output, then the output includes project configuration and prompt files suitable for later sync.
3. Given a generated prompt/module exists, when the user runs `pdd sync <module>`, then PDD syncs that module through the normal single-module sync path.
4. Given the sync target is one module, when PDD materializes code, then it does not silently widen the request to every generated module.
5. Given reviewers inspect the resulting PR, when they trace the synced module, then they can identify the original PRD request and the prompt files that shaped the code.
6. Given this story is reported in coverage, when generate and sync dev units are listed separately, then this story is shown under each linked unit but counted once globally.

## Oracle

These details matter for pass/fail:
- issue/PRD routing to the architecture workflow
- architecture output includes prompt files and project configuration
- sync accepts a generated module target after architecture generation
- single-module sync scope is preserved
- evidence links the generated/synced artifacts to the request
- cross-unit story metadata lists every participating dev unit

## Non-Oracle

These details should not matter:
- exact generated module names or architecture content
- exact provider/model used by generation or sync
- exact console styling or progress wording
- internal helper names below the documented command boundaries

## Negative Cases

- A PRD issue must not be handled as a normal prompt-file generation request.
- `pdd sync <module>` must not ignore the requested module and regenerate the whole project.
- The generated prompt handoff must not lose the issue/request reference needed for review.
- Coverage must not count this one cross-unit story once per linked prompt.

## Non-Goals

- This story does not verify the semantic quality of generated application code.
- This story does not cover incremental PRD mode.
- This story does not prescribe the internal architecture step sequence.

## Candidate Prompts

- `prompts/commands/generate_python.prompt` - owns the public `pdd generate` command surface.
- `prompts/agentic_architecture_python.prompt` - owns the PRD/issue architecture workflow.
- `prompts/sync_main_python.prompt` - owns single-module sync behavior.
- `prompts/commands/maintenance_python.prompt` - owns the public `pdd sync` command surface.
- `prompts/sync_orchestration_python.prompt` - related sync orchestration support.

## Notes

This story is a cross-dev-unit regression oracle for the documented PRD
generate-to-sync workflow in `docs/TUTORIALS.md`.
