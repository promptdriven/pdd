<!-- pdd-story-contract derived-from-story="../story__pdd_sync_conflict_safe_update.md" story-hash="419d7df97e193e9c" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Sync preserves reviewable conflicts

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_sync_conflict_safe_update.md`), not this contract.

## Covers

- R1: Sync detects prompt/code conflicts before applying generated output.
- R2: Conflict detection classifies prompt-side and code-side changes as reviewable conflict evidence.
- R3: Conflict orchestration blocks unsafe overwrites until a resolution path is chosen.
- R4: Resolved conflicts preserve the selected source of truth and discard only reviewed alternatives.
- R5: Final sync evidence distinguishes clean sync, resolved conflict, and blocked conflict states.

## Context

Sync and update are only safe regression tools when they keep conflicting human
and generated edits visible. The conflict-safe sync behavior should be small
enough to test like a unit: detect, classify, preserve, and report.

## Acceptance Criteria

1. Given prompt and code changes disagree, when sync runs, then it detects the conflict before writing replacement output.
2. Given a conflict is detected, when evidence is produced, then it identifies the affected files and conflicting sides.
3. Given no resolution is supplied, when orchestration completes, then the workflow blocks the unsafe overwrite.
4. Given a resolution is supplied, when sync applies it, then only the reviewed source of truth is kept.
5. Given the workflow reports status, when evidence is inspected, then clean, resolved, and blocked conflict states are distinct.

## Oracle

These details matter for pass/fail:
- conflict-safe sync detects prompt/code disagreement before writes
- reviewable conflict evidence identifies affected files and sides
- unsafe overwrites are blocked without resolution
- resolved conflicts preserve the chosen source of truth
- final evidence separates clean, resolved, and blocked outcomes

## Non-Oracle

These details should not matter:
- exact conflict marker text
- exact temporary file names
- exact diff formatting
- whether a resolver is interactive or scripted

## Negative Cases

- Sync must not silently overwrite human prompt edits with generated code.
- Sync must not silently overwrite code edits with stale prompt content.
- A blocked conflict must not be reported as a clean sync.
- Conflict evidence must not disappear before review.

## Non-Goals

- This story does not define a full merge UI.
- This story does not require every possible language-specific conflict parser.
- This story does not merge anything into `main`.

## Candidate Prompts

- `prompts/sync_main_python.prompt` - owns the public sync execution path.
- `prompts/conflicts_in_prompts_python.prompt` - owns prompt conflict detection.
- `prompts/conflicts_main_python.prompt` - owns conflict reporting and status.
- `prompts/sync_orchestration_python.prompt` - owns sync orchestration and resolution flow.

## Notes

This story protects sync and update from losing review context when generated
changes meet human edits.
