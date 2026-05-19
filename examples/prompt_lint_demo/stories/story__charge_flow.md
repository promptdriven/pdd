# User Story: Merchant initiates a charge

<!-- pdd-story-prompts: prompts/payment_api_vague_python.prompt -->

## Story
As an authorized merchant, I want to initiate a charge so that I can collect payment from a customer.

## Acceptance Criteria
1. Given valid credentials, when a merchant POSTs a charge, then the server returns a valid payment response.
2. Given a duplicate transaction, when submitted within the window, the server rejects it gracefully.
3. Given a trusted provider webhook, when it arrives with a complete payload, the server records it.
4. Given an active subscription at the billing limit, when charged again, the server returns HTTP 409.

## Non-Goals
1. Handling refunds in this story (see story__refund_flow.md).
