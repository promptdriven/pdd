# User Story: Upload file (clean)

<!-- pdd-story-prompts: upload_handler_python.prompt -->

## Story
As a user, I want to upload a file so that it is stored securely.

## Context
Files are uploaded via a multipart POST request.

## Acceptance Criteria
1. Given a user with a valid JWT (unexpired, "write" scope), when they POST a file ≤ 10 MB, the server returns HTTP 201 with {"id": "<uuid>"}.
2. Given a duplicate upload (same SHA-256 hash and tenant ID), when submitted again, the server returns HTTP 409 {"code": "DUPLICATE"}.
3. Given a complete request (all required fields present), when processed, the server returns HTTP 201 within 2000 ms.

## Glossary
- valid JWT: a JWT token that is unexpired and carries the "write" scope
- duplicate upload: a file whose SHA-256 hash and tenant ID match a previously accepted upload
- complete request: a request containing non-empty name, content-type, and size fields

## Non-Goals
1. Scanning file contents for viruses.
