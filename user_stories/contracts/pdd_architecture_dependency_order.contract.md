<!-- pdd-story-contract derived-from-story="../story__pdd_architecture_dependency_order.md" story-hash="da3c66129b146eda" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Architecture order drives safe sync

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_architecture_dependency_order.md`), not this contract.

## Covers

- R1: Architecture sync reads dependency metadata from linked prompt and dev-unit records.
- R2: Sync ordering produces a deterministic generation order that respects upstream dependencies.
- R3: Missing dependency metadata and dependency cycles are reported as blockers.
- R4: Metadata synchronization preserves the resolved order and linked unit attribution.
- R5: Re-running the same architecture input produces the same ordered evidence.

## Context

Architecture-driven workflows span registry, ordering, sync, and metadata
updates. A unit-test-like regression needs architecture dependency order to be
explicit so a generated or synchronized unit is not refreshed before the
dependency state it relies on is available.

## Acceptance Criteria

1. Given architecture metadata names dependencies, when sync planning runs, then the plan includes every referenced prompt and dev unit.
2. Given dependencies form an acyclic graph, when ordering runs, then upstream units appear before dependent units.
3. Given a dependency is missing or cyclic, when planning runs, then the workflow reports a blocker instead of guessing an order.
4. Given metadata sync completes, when evidence is inspected, then the linked units and resolved order are visible.
5. Given inputs are unchanged, when planning is repeated, then the generated order and evidence are stable.

## Oracle

These details matter for pass/fail:
- architecture dependency order is derived from explicit metadata
- generation order is deterministic and dependency-aware
- missing or cyclic dependencies are blockers
- metadata sync records the resolved unit attribution
- unchanged inputs produce unchanged order evidence

## Non-Oracle

These details should not matter:
- exact internal graph data structure
- exact ordering of independent sibling units
- cosmetic wording of blocker messages
- exact location of cached architecture metadata

## Negative Cases

- A dependent unit must not be generated before its upstream source unit.
- A dependency cycle must not silently fall back to file-system order.
- Missing architecture metadata must not be treated as successful sync.
- Metadata sync must not drop linked dev-unit attribution.

## Non-Goals

- This story does not prescribe a visual architecture diagram.
- This story does not require live LLM generation during deterministic checks.
- This story does not merge anything into `main`.

## Candidate Prompts

- `prompts/architecture_sync_python.prompt` - owns architecture sync behavior.
- `prompts/sync_order_python.prompt` - owns dependency-aware ordering.
- `prompts/architecture_registry_python.prompt` - owns registered architecture metadata.
- `prompts/metadata_sync_python.prompt` - owns metadata synchronization.

## Notes

This story turns architecture ordering into a small regression oracle that can
fail independently of the larger sync workflow.
