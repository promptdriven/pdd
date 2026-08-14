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

- module: <module: value copied verbatim from primary_prompt_interfaces, or `none`>
- callable: <a name from that block's functions: list, or `none`>
- args: []
- kwargs: {}

## Seams

Optional runtime-boundary patches for deterministic behavioral tests:
- <dotted.import.path> = <Python literal>

## Oracle

Each bullet is an executable Python boolean expression over `result` (the Entry
Point's return value) — not prose. These decide pass/fail:
- result.status == "ok"
- isinstance(result, dict)
- result.get("event") == "emitted"
- "error" not in result

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

Each bullet is the same kind of boolean expression over `result`, protecting
against a forbidden outcome (e.g. `result.get("called_llm") is False`).

## Non-Goals

What this story explicitly does not cover.

## Candidate Prompts

Other prompts in this codebase the story could also be run against:
- `prompts/<module>_<language>.prompt` — <one-line reason> (primary)
- `prompts/<other>_<language>.prompt` — <one-line reason> (related|possible)

## Notes

Links, edge cases, fixtures, rationale, or issue-pinned constraints.
