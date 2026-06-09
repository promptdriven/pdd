<!-- pdd-story-prompts: prompts/<module>_<language>.prompt -->

# User Story: <name>

## Story

As a <persona>,
I want <behavior>,
so that <value>.

<!--
The Story above is the ONLY part a human reads and signs off on. Keep it one
plain-language promise about user-facing behavior — no flags, exit codes, or
internals. Describe the user's stable goal and what they can do/see; never pin it
to a specific external product/tool/UI ("like Claude Code's UI") or to a
time-/version-sensitive fact, so it survives the ecosystem changing.

Everything under "## LLM-Confirmed Contract" is machine-checkable evidence that
`pdd detect --stories` / the LLM verifies against the prompts. Humans may skim it
but are not asked to verify it line-by-line.
-->

## LLM-Confirmed Contract

### Covers

- R1: <contract rule name>
- R2: <contract rule name>

### Context

Describe relevant state, assumptions, fixtures, users, records, external services, or dependencies.

### Acceptance Criteria

1. Given ..., when ..., then ...
2. Given ..., when ..., then ...

### Oracle

These details matter for pass/fail:
- error type
- state transition
- absence/presence of external call
- emitted event
- returned value shape

### Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering
- resemblance to any specific third-party tool's UI or behavior
- which provider/model is currently considered "best"
- cosmetic styling that tracks fashion (exact colors, pixel layout)

### Negative Cases

List forbidden outcomes this story protects against.

### Non-Goals

What this story explicitly does not cover.

### Notes

Links, edge cases, fixtures, rationale, or implementation hints.
