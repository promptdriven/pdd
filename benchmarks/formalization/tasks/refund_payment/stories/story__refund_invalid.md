<!-- pdd-story-prompts: refund_payment_python.prompt -->

# Story: Refund Rejection for Invalid Amounts

As a payment operations engineer,
I want the refund service to reject zero and over-limit refund requests,
so that invalid refunds never reach the payment provider.

## Acceptance Criteria

- Given a refund request with amount = 0.00, the service returns HTTP 422.
- Given a refund request with amount > original charge, the service returns HTTP 422.
- In both cases, no call is made to the payment provider API.

## Covers

- R1: zero-amount refund is rejected before processing
- R2: over-refund amount is rejected before processing

## Oracle

These details matter for pass/fail:

- HTTP status 422 for invalid amounts
- Payment provider API must not be called when validation fails

## Non-Oracle

Internal helper names and exact log wording (beyond HTTP status) should not affect pass/fail.

## Notes

These checks happen synchronously in the validation layer, before any I/O.
