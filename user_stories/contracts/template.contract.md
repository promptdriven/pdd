<!-- pdd-story-contract derived-from-story="../story__<name>.md" story-hash="<auto>" issue-ref="<url|number|path>" -->

# Contract: <name>

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__<name>.md`), not this contract.

## Covers

- R1: <contract rule name>
- R2: <contract rule name>

## Context

Describe relevant state, assumptions, fixtures, users, records, external services, or dependencies.

## Acceptance Criteria

1. Given ..., when ..., then ...
2. Given ..., when ..., then ...

## Oracle

These details matter for pass/fail:
- error type
- state transition
- absence/presence of external call
- emitted event
- returned value shape

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering
- resemblance to any specific third-party tool's UI or behavior
- which provider/model is currently considered "best"
- cosmetic styling that tracks fashion (exact colors, pixel layout)

## Negative Cases

List forbidden outcomes this story protects against.

## Entry Point

Optional. Required only when this contract's story is consumed by
`pdd test --from-story`. Name the callable the generated tests drive in-process:
- `pdd.<module>:<callable>`

## Seams

Optional. Boundaries the generated tests monkeypatch to stay offline/deterministic:
- `pdd.<module>:<boundary_callable>` — <one-line reason (e.g. LLM/cloud call)>

## Non-Goals

What this story explicitly does not cover.

## Candidate Prompts

Other prompts in this codebase the story could also be run against:
- `prompts/<module>_<language>.prompt` — <one-line reason> (primary)
- `prompts/<other>_<language>.prompt` — <one-line reason> (related|possible)

## Notes

Links, edge cases, fixtures, rationale, or issue-pinned constraints.
