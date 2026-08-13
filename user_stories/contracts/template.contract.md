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

## Entry Point

Declaring this section is what makes `pdd test --from-story` generate a
*behavioural* test — one that imports the callable, invokes it, and asserts the
`## Oracle` / `## Negative Cases` below as Python expressions over `result`.
Omit the section and the generated test only pins this document's text; it will
not execute the code the story is about.

Declare it completely or not at all: a partial block (missing `- module:` or
`- callable:`) is rejected rather than silently downgraded.

- module: package.module
- callable: function_name
- args: []
- kwargs: {}

## Seams

Optional. Assignments applied before the call, to pin values the story does not
control (clocks, rates, IDs) so the oracle stays deterministic.

- package.module.SOME_CONSTANT = 0

## Oracle

These details matter for pass/fail.

When `## Entry Point` is declared, write these as Python expressions over
`result` (e.g. `result["total"] == 3`) — they are evaluated against the live
return value. Without an Entry Point they are prose, and are only recorded.

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

## Non-Goals

What this story explicitly does not cover.

## Candidate Prompts

Other prompts in this codebase the story could also be run against:
- `prompts/<module>_<language>.prompt` — <one-line reason> (primary)
- `prompts/<other>_<language>.prompt` — <one-line reason> (related|possible)

## Notes

Links, edge cases, fixtures, rationale, or issue-pinned constraints.
