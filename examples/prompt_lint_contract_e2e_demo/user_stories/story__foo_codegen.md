<!-- pdd-story-prompts: prompts/foo_codegen_python.prompt -->

# User Story: Idempotent foo_work handler (codegen + lint fixture)

Covers observable rules R1–R4 on the codegen prompt. R5–R6 stay vague in the
prompt on purpose (not listed here).

## Covers

- R1: fresh idempotency key with active authorized user returns HTTP 200
- R2: replay within 24 hours returns HTTP 409 with reason and original_request_id
- R3: missing or invalid Bearer JWT returns HTTP 401
- R4: inactive user returns HTTP 403

## Acceptance Criteria

- Given a valid JWT with scope foo:invoke and an active user, when X-Idempotency-Key is new, then HTTP 200 with `result` and `request_id` and the key is stored once.
- Given the same X-Idempotency-Key within 24 hours, when invoked again, then HTTP 409 with `reason` and `original_request_id` and no second store entry.
- Given no Authorization header, when processed, then HTTP 401.
- Given last login older than 5 days, when processed with valid JWT, then HTTP 403.
