# User Story: Charge a payment card

<!-- pdd-story-prompts: payment_api_clean_python.prompt -->

## Story
As a merchant, I want to charge a customer's card via POST /charge,
so that I receive a confirmed payment receipt.

## Acceptance Criteria
1. Given an authorized principal with a valid amount (100 cents),
   when POST /charge is called with idempotency_key "k1",
   then the server returns HTTP 200 with a successful charge receipt.
2. Given an unauthorized principal,
   when POST /charge is called,
   then the server returns HTTP 403 with {"code": "FORBIDDEN"}.
3. Given a duplicate transaction (same idempotency_key + merchant_id),
   when POST /charge is called again,
   then the server returns HTTP 200 with the existing charge record (no new row).
4. Given a provider failure (upstream HTTP 500),
   when POST /charge is called,
   then the server returns a graceful provider failure response (HTTP 502).

## Covers
- R1: amount validation
- R2: authorized callers only
- R3: duplicate idempotency
- R4: success response
- R5: graceful error handling

## Glossary
- valid amount: a positive integer in the smallest currency unit (e.g. cents),
  greater than 0 and at most 99_999_999
- authorized principal: a caller whose Bearer JWT contains scope "charge:write"
  and whose sub claim matches a registered merchant ID
- unauthorized principal: any caller that does not meet the authorized principal definition
- duplicate transaction: a charge whose idempotency_key and merchant_id match
  a row in charges with status IN ("pending", "succeeded")
- successful charge receipt: HTTP 200 with JSON {"id": "<uuid>", "status": "succeeded"}
- graceful provider failure: HTTP 502 with JSON {"code": "PROVIDER_ERROR"}
