# User Story: Upload file with ## Covers vocabulary

<!-- pdd-story-prompts: upload_handler_python.prompt -->

## Story
As a user, I want to upload a file so that it is stored securely.

## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, the server returns HTTP 201.
2. Given a duplicate upload, when submitted by the same tenant, the server returns HTTP 409.
3. Given an active user who has reached their daily limit, when they upload, the server returns HTTP 429.

## Covers
- authorized user: a user whose Bearer JWT is present, unexpired, and carries the "upload" scope
- valid file: a file whose MIME type is in the allowlist and whose size is ≤ 10 MB
- duplicate upload: an upload whose SHA-256 hash and tenant ID match a previously accepted upload
- active user: a user whose account.status field equals "active" in the accounts table

## Non-Goals
1. Virus scanning file contents.
