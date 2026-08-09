# User Story: Payment charge flow

<!-- pdd-story-prompts: payment_api_clean_python.prompt -->

## Story
As an authorized merchant, I want to submit a charge so that my customer is billed correctly.

## Acceptance Criteria
1. Given an authorized merchant, when they submit a charge with a valid payment method and a unique idempotency_key, then the system returns HTTP 201 with a charge ID.
2. Given an authorized merchant, when they submit a duplicate charge (same idempotency_key within 24 hours), then the system returns HTTP 409 with the original charge ID.
3. Given a suspicious transaction (risk_score > 0.85), when submitted by any merchant, then the system rejects the request with HTTP 422.
4. Given a settled charge, when queried by the merchant, then the system returns the settled_at timestamp.

## Covers
- R1: idempotency_key uniqueness enforced within 24-hour window
- R2: authorized merchant holds a non-expired API key with payments:write scope
- R4: suspicious transaction has risk_score exceeding the 0.85 threshold
- R5: successful charge reaches status=captured with HTTP 201
- R6: settlement event emitted to audit queue on status transition
