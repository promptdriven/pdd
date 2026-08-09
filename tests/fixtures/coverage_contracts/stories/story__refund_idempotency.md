<!-- pdd-story-prompts: refund_payment_python.prompt -->

# Story: Refund Retry Idempotency

As a payment operations engineer,
I want refund retries to reuse the original idempotency key,
so that duplicate network retries do not create duplicate refunds.

## Acceptance Criteria

- Given a refund request with refund_id="ref_abc123", the idempotency key
  is derived from the refund_id on all subsequent retry attempts.
- The service returns the same refund record for duplicate requests within
  the idempotency window.

## Covers

- R4: idempotency key is reused on retry

## Notes

No automated test exists for this story yet; manual QA verified in staging.
