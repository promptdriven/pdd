# User Story: Prompt lint upload sample

<!-- pdd-story-prompts: prompts/foo_python.prompt -->

## Story

As an upload API consumer,
I want duplicate uploads to be handled consistently,
so that retries do not create duplicate records.

## Acceptance Criteria

1. Given a user with an unexpired Bearer token whose scope includes `upload:write`, when they upload a PNG file that is 2 MB, then the API returns HTTP 201 and writes one upload record.
2. Given an upload whose tenant ID and SHA-256 hash match a previously accepted upload, when the same tenant submits it again, then the API returns HTTP 409 and writes no new upload record.
3. Given a request with `tenant_id`, `filename`, `content_type`, `size_bytes`, and `sha256`, when all fields satisfy the upload schema, then the API returns HTTP 201 with a JSON body containing `upload_id`.

## Glossary

- authorized user: a user with an unexpired Bearer token whose scope includes `upload:write`
- valid file: a file whose MIME type is in the allowlist and whose size is at most 10 MB
- duplicate upload: an upload whose tenant ID and SHA-256 hash match a previously accepted upload
- complete request: a request containing `tenant_id`, `filename`, `content_type`, `size_bytes`, and `sha256`
- successful response: HTTP 201 with a JSON body containing `upload_id`
