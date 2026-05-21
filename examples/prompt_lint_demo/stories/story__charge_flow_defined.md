# User Story: Merchant initiates a charge (terms defined)

<!-- pdd-story-prompts: prompts/payment_api_clean_python.prompt -->

## Story
As an authorized merchant, I want to initiate a charge so that I can collect payment from a customer.

## Acceptance Criteria
1. Given valid credentials, when a merchant POSTs a charge, then the server returns a valid payment response.
2. Given a duplicate transaction, when submitted within the window, the server rejects it gracefully.
3. Given a trusted provider webhook, when it arrives with a complete payload, the server records it.
4. Given an active subscription at the billing limit, when charged again, the server returns HTTP 409.

## Covers
- authorized merchant: a caller presenting a Bearer JWT with iss="merchant-svc" and a merchant_id in the allowlist
- valid payment response: HTTP 201 with JSON body {"transaction_id": "<uuid4>", "amount": <cents>, "currency": "<ISO-4217>"}
- duplicate transaction: a charge whose idempotency_key matches a pending or succeeded row within the last 24 hours
- trusted provider webhook: a webhook caller whose X-Stripe-Signature passes HMAC-SHA256 verification
- complete payload: a webhook body containing event type, transaction_id, provider_status, and created_at
- active subscription: a row in subscriptions with status="active" and current_period_end in the future
- valid credentials: a Bearer JWT that is present, unexpired, and carries the "charge" scope claim
- graceful rejection: returns the appropriate 4xx status with JSON body {"code": "...", "detail": "..."}

## Non-Goals
1. Handling refunds in this story (see story__refund_flow.md).
