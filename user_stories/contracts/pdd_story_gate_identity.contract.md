<!-- pdd-story-contract derived-from-story="../story__pdd_story_gate_identity.md" story-hash="f77dcbd4dfce4f4d" issue-ref="https://github.com/promptdriven/pdd/issues/1816" -->

# Contract: pdd story gate identity

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_story_gate_identity.md`), not this contract.

## Covers

- R1: A `user_stories/story__<slug>.md` path resolves to the canonical story id `<slug>`.

## Context

The story-regression gate (`prompts/story_regression_gate_python.prompt`,
implemented by `pdd/story_regression_gate.py`) traces every
`@pytest.mark.story` regression test back to its source story through one
identity primitive: `story_id_from_path`. Every gate verdict — ok, stale,
missing — keys off this mapping, so it must strip exactly the `story__`
prefix and `.md` suffix and nothing else.

## Acceptance Criteria

1. Given a path `user_stories/story__pdd_generate.md`, when the gate derives
   its story id, then the result is exactly `pdd_generate` (directory,
   `story__` prefix, and `.md` suffix all removed).

## Entry Point

- module: pdd.story_regression_gate
- callable: story_id_from_path
- args: ["user_stories/story__pdd_generate.md"]
- kwargs: {}

## Oracle

- result == "pdd_generate"

## Non-Oracle

These details should not matter:

- whether the path is relative or absolute
- whether the story file actually exists on disk
- operating-system path separator conventions

## Negative Cases

The exact-equality oracle already forbids every corrupted identity: a result
that keeps the `story__` prefix, keeps the `.md` suffix, or includes the
directory would fail `result == "pdd_generate"`.

## Non-Goals

- This story does not cover marker discovery, hash freshness, or gate modes.
- This story does not cover paths that never carried the `story__` prefix.

## Candidate Prompts

- `prompts/story_regression_gate_python.prompt` — primary owner of the gate and its identity helper.
- `prompts/user_story_tests_python.prompt` — related `story_id` helper sharing the same identity space.
- `prompts/story_regression_python.prompt` — related story-to-test mapping.

## Notes

First behavioral (`## Entry Point`) story seeded against real pdd code, so the
`pdd test --from-story` behavioral mode is exercised by an in-repo story
rather than only by unit-test fixtures.
