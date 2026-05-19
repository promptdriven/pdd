<!-- pdd-story-prompts: refund_payment_python.prompt -->

# User Story: Invalid refunds are rejected before provider calls

## Covers

- R1: zero and negative refund amounts are rejected
- R2: over-refund amounts are rejected

## Story

As a payment operations engineer,
I want invalid refund requests rejected before provider calls,
so that customer balances and provider state remain consistent.

## Acceptance Criteria

- Given a refund amount of zero, when the refund is requested, then the service returns HTTP 422.
- Given a refund amount greater than the original charge, when the refund is requested, then the service returns HTTP 422.

## Oracle

- The returned status is HTTP 422.
- No provider refund API call is made.

