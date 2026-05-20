<!-- pdd-story-prompts: prompts/foo_formalized_python.prompt -->

# Foo handler idempotency — FORMALIZED story

Companion story for the *positive* fixture
(`prompts/foo_formalized_python.prompt`). Covers all four rules and defines
the shared vocabulary in a `## Glossary` block, so deterministic coverage
reaches `checked`/`story-only` for every rule without any tests yet.

## Covers

prompts/foo_formalized_python.prompt#R1
prompts/foo_formalized_python.prompt#R2
prompts/foo_formalized_python.prompt#R3
prompts/foo_formalized_python.prompt#R4

## Glossary

- active user: a user whose request_received_at - last_login_at <= 5 days
- duplicate request: a request whose X-Idempotency-Key matches a previously
  accepted request within the last 24 hours
- authorized caller: a caller presenting a Bearer JWT whose exp is in the
  future and whose scope includes "foo:invoke"
- valid response: HTTP 200 with body matching {result: object}
- duplicate response: HTTP 409 with body matching
  {reason: string, original_request_id: uuid}

## Acceptance Criteria

- Given an authorized caller who is an active user and whose
  X-Idempotency-Key has not been seen in the last 24 hours, when they
  submit a request, then the handler returns HTTP 200 and writes one
  request record.
- Given a request whose X-Idempotency-Key has been seen in the last 24
  hours, when the same caller submits it again, then the handler returns
  HTTP 409 with reason and original_request_id and writes no new record.
- Given a caller with a missing, expired, or out-of-scope Bearer JWT, when
  they submit a request, then the handler returns HTTP 401 and writes no
  record.
- Given an authorized caller whose request_received_at - last_login_at is
  greater than 5 days, when they submit a request, then the handler
  returns HTTP 403 and writes no record.
