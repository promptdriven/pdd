<!-- pdd-story-contract derived-from-story="../story__pdd_feature_change_pr.md" story-hash="116740a5ec1b111d" issue-ref="https://github.com/promptdriven/pdd/issues/1769" -->

# Contract: Feature request becomes a verified PDD change PR

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_feature_change_pr.md`), not this contract.

## Covers

- R1: GitHub feature issues route through `pdd change` rather than manual patch mode.
- R2: The change workflow identifies and updates the prompt/dev units that own the requested behavior.
- R3: Generated user-story artifacts include both the human story and contract sidecar.
- R4: Step comments and final status make degraded-vs-failed workflow state visible to reviewers.
- R5: The created PR includes enough evidence for reviewers to connect issue, prompts, stories, and verification.
- R6: The cross-dev-unit story is attributed to change command, orchestration, shared agentic utilities, story generation, and contract generation without duplicate global counting.

## Context

The documented feature workflow starts from `pdd change <issue-url>`, updates
the prompt source of truth, adds or updates user stories for product-level
behavior, verifies the result, and opens a PR. This crosses the command layer,
agentic change orchestration, shared agentic GitHub comments, and story/contract
generation.

## Acceptance Criteria

1. Given a GitHub feature issue, when the user runs `pdd change <issue-url>`, then PDD routes to the issue-driven agentic change workflow with GitHub-state and restart controls.
2. Given the workflow determines the affected dev units, when it edits the repository, then prompt changes remain the durable source of truth rather than only patching generated code.
3. Given the change creates or updates a user story, when artifacts are staged, then the human story and generated contract sidecar travel together.
4. Given a recoverable agentic step fails, when the workflow reports status, then reviewers can distinguish degraded continuation from a terminal failure.
5. Given the workflow completes, when the PR is created, then its evidence links the issue, changed prompts, story files, contract files, and verification commands.
6. Given coverage reports this story, when each linked dev unit is listed, then this story appears under every linked unit but is counted once globally.

## Oracle

These details matter for pass/fail:
- issue URL routing to agentic change
- prompt-source updates rather than code-only patches
- paired story and contract sidecar artifacts
- visible workflow status semantics
- PR evidence connecting issue, prompts, stories, and verification
- cross-unit metadata lists every participating dev unit

## Non-Oracle

These details should not matter:
- exact prompt prose chosen by the workflow
- exact generated PR body wording beyond evidence presence
- exact provider/model selected
- exact console colors or progress formatting

## Negative Cases

- A feature issue must not silently route to manual change mode.
- The workflow must not stage a story without its contract sidecar when one was generated.
- A recoverable step failure must not be reported as a terminal workflow abort.
- Coverage must not count this one cross-unit story once for each linked prompt.

## Non-Goals

- This story does not prescribe the exact prompt patch.
- This story does not cover `pdd bug` or `pdd fix`.
- This story does not verify downstream CI provider behavior.

## Candidate Prompts

- `prompts/commands/modify_python.prompt` - owns the public `pdd change` command surface.
- `prompts/agentic_change_orchestrator_python.prompt` - owns the multi-step change workflow.
- `prompts/agentic_change_python.prompt` - owns change workflow behavior.
- `prompts/user_story_tests_python.prompt` - owns story generation/linking support.
- `prompts/generate_story_contract_LLM.prompt` - owns generated contract sidecars.
- `prompts/agentic_common_python.prompt` - related shared issue/PR status support.

## Notes

This story is a cross-dev-unit regression oracle for the documented
issue-driven feature workflow in `docs/TUTORIALS.md` and
`docs/prompting_guide.md`.
