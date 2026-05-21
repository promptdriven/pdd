<!-- pdd-story-prompts: refund_payment_python.prompt -->

# User Story: Refund retries are idempotent

## Covers

- R4: retries reuse the original idempotency key

## Story

As a payment operations engineer,
I want refund retries to reuse the original idempotency key,
so that transient network failures do not create duplicate refunds.

## Acceptance Criteria

- Given a retry with an existing refund ID, when the request is sent, then the same idempotency key is used.

## Oracle

- The provider call receives the original idempotency key.

