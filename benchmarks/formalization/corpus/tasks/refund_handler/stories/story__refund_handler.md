<!-- pdd-story-prompts: tasks/refund_handler/A0.prompt -->

# Story: Refunds are idempotent and restricted to active users

As a payments engineer,
I want refund requests to be idempotent and authorized,
so that duplicate or invalid refunds never reach the provider.

## Covers

- R1: only active users may receive refunds
- R2: repeating the same refund id returns the same outcome
- R3: unauthorized users are rejected
- R4: invalid amounts are rejected
- R5: successful refunds return a receipt identifier

## Acceptance Criteria

- Given an inactive user, refund is rejected.
- Given duplicate refund_id, the second call matches the first outcome.
- Given a valid active-user refund, a receipt id is returned.

## Oracle

These details matter for pass/fail:

- ok vs rejected outcome
- receipt identifier present on success
- idempotent repeat returns identical payload

## Non-Oracle

These details should not matter:

- internal storage mechanism for processed ids
- exact receipt id prefix string beyond uniqueness
- private method names on the handler

## Notes

Hand-authored gold corpus story for benchmark oracle evaluation (#820 template).
