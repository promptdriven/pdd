<!-- pdd-story-prompts: tasks/token_bucket/A0.prompt -->

# Story: Token bucket allows requests until empty then refills

As a platform engineer,
I want a token-bucket rate limiter with burst capacity,
so that traffic spikes are absorbed without overloading downstream services.

## Covers

- R1: allowed request returns True and decrements tokens
- R2: empty bucket rejects with False
- R3: tokens refill at a steady rate over time
- R4: duplicate request ids within a window are handled safely

## Acceptance Criteria

- Given tokens available, allow() returns True.
- Given an empty bucket, allow() returns False until refill.
- Given the same request id twice, behavior remains safe (no double-charge).

## Oracle

These details matter for pass/fail:

- boolean allow/deny outcome
- token count decreases on allowed requests
- refill increases tokens over elapsed time

## Non-Oracle

These details should not matter:

- internal clock implementation (monotonic vs wall)
- class vs functional API shape
- exact variable names for bucket state

## Notes

Hand-authored gold corpus story for benchmark oracle evaluation (#820 template).
