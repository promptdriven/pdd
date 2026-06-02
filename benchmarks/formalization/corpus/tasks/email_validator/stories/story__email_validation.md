<!-- pdd-story-prompts: tasks/email_validator/A0.prompt -->

# Story: Email validation accepts valid addresses and rejects invalid ones

As a backend engineer,
I want email strings validated before persistence,
so that malformed addresses never enter the system.

## Covers

- R1: valid email returns True
- R2: invalid email returns False
- R3: empty input is rejected safely

## Acceptance Criteria

- Given a well-formed email, validation returns True.
- Given malformed or empty input, validation returns False.

## Oracle

These details matter for pass/fail:

- boolean return value (True vs False)
- empty or whitespace-only input is rejected
- exactly one `@` in the address

## Non-Oracle

These details should not matter:

- private helper or class names
- exact wording of internal error messages
- whether validation uses regex vs procedural checks

## Notes

Hand-authored gold corpus story for benchmark oracle evaluation (#820 template).
