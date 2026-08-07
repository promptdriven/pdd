<!-- pdd-story-contract derived-from-story="../story__pdd_generation_gates_preserved.md" story-hash="e845346c81899424" issue-ref="user_stories/issues/conformance-gate-split.md" -->

# Contract: Generation safety checks must survive PDD's own internal reorganisation

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_generation_gates_preserved.md`), not this contract.

## Covers
- AC1: Report output-shape problems (non-code) distinctly from symbol-conformance errors.
- AC2: Refuse removal or reshaping of public symbols by naming the symbol and its expected shape.
- AC3: Refuse writes that exceed the test-churn threshold for existing test files.
- AC4: Ensure target files on disk remain unchanged if any safety check fails.
- AC5: Maintain existing override/opt-in mechanisms (directives) without lowering the barrier to entry.

## Context
A development environment where PDD is used to generate or regenerate code files based on prompts. The system has existing safety gates: `declared_surface`, `test_churn`, `interface_check`, and `directives`.

## Acceptance Criteria
1. Given a model response that contains planning text or an apology instead of code, when generation is run, then PDD must report an output-shape error and the target file must remain unchanged.
2. Given a prompt that defines a public interface, when a regeneration attempt removes an existing function or changes its signature, then PDD must refuse the write and name the specific regressing symbol and its required shape.
3. Given an existing test file, when a regeneration would rewrite more than the allowed percentage of lines, then PDD must refuse the write unless a specific override directive is present.
4. Given a failing safety check, when the generation process terminates, then the file on disk must be identical to its state before the process began (no truncation, no partial writes).
5. Given a safety check override (e.g., a BREAKING-CHANGE directive), when internal PDD code is reorganized, then the override must still require the same explicit user opt-in to function.

## Oracle
These details matter for pass/fail:
- The distinction between "output is not code" and "code is missing a symbol" in error reporting.
- The presence of the specific symbol name and its expected signature in the regression error message.
- The failure to write to disk (file hash remains constant) upon any gate violation.
- The requirement for an explicit directive to bypass churn or interface gates.
- Specific typed exceptions (as defined in `gate_errors_python.prompt`) being raised for different failure modes.

## Non-Oracle
These details should not matter:
- The internal file structure or module organization of the PDD codebase itself.
- The exact wording of error messages, provided the required identifiers (symbol name, shape, error type) are present.
- The specific model used to generate the output.
- Performance or latency of the check execution.

## Negative Cases
- A safety check silently passes (no-op) when it should have blocked a change.
- A failing check results in a truncated or partially overwritten file.
- An override directive for one check (e.g., churn) accidentally suppresses a different check (e.g., interface shape).
- Multiple distinct failure types are collapsed into a single generic "Generation failed" error.

## Non-Goals
- Adding new types of safety checks.
- Changing existing threshold values or default configurations.
- Modifying the syntax of how a user opts out of a check.

## Candidate Prompts
- `gate_errors_python.prompt` — Defines the typed exceptions that ensure errors remain distinguishable (primary)
- `declared_surface_python.prompt` — Implements the public-surface regression gate (primary)
- `test_churn_python.prompt` — Implements the test-file protection gate (primary)
- `interface_check_python.prompt` — Implements the symbol/export conformance gate (primary)
- `directives_python.prompt` — Defines the grammar for deliberate overrides (primary)

## Notes
- This contract ensures that the "Safety Net" of PDD remains intact during refactoring of the PDD core.
- Error types and behaviors are pinned to the requirements in the original issue to prevent regression of user trust during internal reorganization.
