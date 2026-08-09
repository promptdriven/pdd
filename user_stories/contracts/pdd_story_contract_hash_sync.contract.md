<!-- pdd-story-contract derived-from-story="../story__pdd_story_contract_hash_sync.md" story-hash="d6aaf845ef5f242b" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Story edits invalidate stale contracts

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_story_contract_hash_sync.md`), not this contract.

## Covers

- R1: User-story tests compute a story contract hash from human story content while ignoring attribution metadata.
- R2: Contract generation writes the current story hash and issue reference into the sidecar header.
- R3: Coverage checks detect a stale contract when the story changes without sidecar synchronization.
- R4: Regenerating or updating the sidecar clears the stale contract only when coverage still satisfies required rules.
- R5: Verification attributes the synchronized story and contract to every linked dev unit.

## Context

The PDD user-story feature depends on a trustworthy link between human story
text and generated contract sidecars. A stale contract should fail fast the same
way a stale unit-test snapshot would fail after fixture input changes.

## Acceptance Criteria

1. Given a story has metadata and body text, when the hash is computed, then only the human story content drives the hash.
2. Given a contract is generated, when its header is inspected, then it contains the current story hash and issue reference.
3. Given a human story changes, when the sidecar still has the old hash, then verification reports a stale contract.
4. Given the sidecar is regenerated, when coverage is still complete, then verification passes.
5. Given a story names multiple dev units, when verification reports attribution, then every linked unit remains covered.

## Oracle

These details matter for pass/fail:
- story contract hash is based on human story content
- generated sidecars carry the current hash and issue reference
- stale contract headers fail deterministic verification
- coverage must still satisfy required rules after regeneration
- linked dev-unit attribution is preserved

## Non-Oracle

These details should not matter:
- exact hash algorithm beyond deterministic behavior and configured length
- cosmetic contract wording
- exact order of non-required notes
- whether regeneration is LLM-backed or fixture-backed in local checks

## Negative Cases

- Editing metadata alone must not invalidate a contract that still matches the story body.
- Editing story body text must not leave an old sidecar hash passing.
- Regeneration must not clear a stale hash by dropping required coverage rules.
- Multi-unit attribution must not collapse to a single owning prompt.

## Non-Goals

- This story does not require live LLM calls in the regression test.
- This story does not prescribe a permanent contract file format beyond the existing header.
- This story does not merge anything into `main`.

## Candidate Prompts

- `prompts/user_story_tests_python.prompt` - owns deterministic user-story verification.
- `prompts/generate_story_contract_LLM.prompt` - owns generated contract content.
- `prompts/coverage_contracts_python.prompt` - owns coverage reporting and stale contract evidence.

## Notes

This story makes story/contract synchronization itself part of the regression
suite, comparable to snapshot tests with explicit fixture hashes.
