<!-- pdd-story-prompts: sync_determine_operation_python.prompt -->
<!-- pdd-story-dev-units: sync_determine_operation_python.prompt -->

# User Story: Nested prompt resolution stays safe and deterministic

## Story

As a PDD maintainer working in a nested project, I want sync to resolve the
requested prompt and its artifacts from one valid project context, so that it
never borrows a sibling module, escapes the project, or repeats expensive tree
scans.

## Covers

- R1: Supported architecture registries map the requested module to its artifact paths and malformed registries fail closed.
- R2: Architecture hints keep the prompt and code aligned with the requested basename and context.
- R3: Project metadata resolution is independent of the process working directory.
- R4: Case-insensitive prompt discovery preserves on-disk casing and deterministic selection.
- R5: Heuristic architecture rows cannot borrow targets from sibling or indeterminate contexts.
- R6: Proven owners retain shared targets unless the resolved target belongs to a sibling context.
- R7: Traversal, absolute escapes, and symlink escapes are rejected before artifact selection.
- R8: Returned prompt paths remain in the allowed prompt or project boundary.
- R9: Non-portable path components are rejected across caller, architecture, and output inputs.
- R10: Degenerate and non-canonical path spellings are rejected.
- R11: Multiple valid outputs for one requested module produce an explicit ambiguity error.
- R12: One resolution observes one coherent architecture snapshot.
- R13: Missing or non-string architecture filenames fall back to the code filepath stem.
- R14: Unvalidated path input cannot forge or split logs.
- R15: New-module paths stay in the resolved nested context without duplicating its prefix.
- R16: Code, example, and test outputs remain inside the governing project boundary.
- R17: Sync lock files remain inside the locks directory for every caller input.
- R18: Recursive fallback enumerates each on-disk prompt at most once per resolution.

## Acceptance Criteria

1. Given a nested context with matching architecture and prompt metadata, when sync resolves a module from any working directory, then prompt, code, example, and test paths all belong to that context.
2. Given sibling, malformed, ambiguous, non-canonical, non-portable, traversal-bearing, or symlink-escaping metadata, when resolution runs, then it rejects or ignores the violating candidate according to R1-R17 and never selects or creates an out-of-bound artifact.
3. Given architecture metadata is atomically replaced during resolution, when a result is returned, then its prompt and code paths both come from one entire pre- or post-replacement snapshot.
4. Given direct lookup misses among N prompt files, when fallback discovery runs, then no more than N prompt entries are enumerated and the context-aligned nested prompt is still selected.
5. Given identical files and configuration, when resolution is repeated, then it returns the same on-disk path casing and ambiguity outcome.

## Oracle

These details matter for pass/fail:

- the resolved prompt and every artifact are in the intended governing context and project boundary
- unsafe or ambiguous inputs fail closed without creating out-of-bound files
- architecture-derived prompt/code pairs come from one coherent snapshot
- returned paths preserve deterministic on-disk casing
- one fallback resolution performs at most one aggregate prompt-tree enumeration

## Non-Oracle

These details should not matter:

- private helper names or internal index data structures
- directory enumeration order before deterministic normalization
- exact exception wording or logging format after inputs are validated
- whether a safe direct lookup avoids building the fallback index entirely

## Forbidden Outcomes

- A nested request resolves a same-named prompt or artifact owned by a sibling context.
- A traversal, non-portable component, or symlink causes a prompt, artifact, or lock file to escape its allowed boundary.
- A resolution returns a prompt from one architecture snapshot and code from another.
- A fallback miss repeatedly walks the same prompt tree.
- Raw unvalidated path content appears in logs.

## Non-Goals

- This story does not change generation, verification, or conflict-analysis decisions after paths are resolved.
- This story does not prescribe an internal cache implementation.

## Candidate Prompts

- `pdd/prompts/sync_determine_operation_python.prompt` — owns nested prompt and artifact resolution (primary).

## Notes

The deterministic resolver regressions are the executable oracle; no live model
or external service is required.
