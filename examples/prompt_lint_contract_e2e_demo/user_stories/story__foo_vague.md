<!-- pdd-story-prompts: prompts/foo_vague_python.prompt -->

# Foo handler idempotency — VAGUE companion story

Companion story for the *negative* fixture
(`prompts/foo_vague_python.prompt`). Intentionally minimal: covers only R1
and R2, with no glossary, so deterministic coverage reports R3/R4 as
`unchecked`.

## Covers

prompts/foo_vague_python.prompt#R1
prompts/foo_vague_python.prompt#R2

## Acceptance Criteria

- Given an active user with last_login within 5 days of request_received_at,
  when the handler runs, then it returns HTTP 200 OK.
- Given a duplicate X-Idempotency-Key within 24 hours, when the handler
  runs, then it returns HTTP 409 with reason and original_request_id.
