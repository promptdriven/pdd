# User Story: Upload file

<!-- pdd-story-prompts: upload_handler_python.prompt -->

## Story
As a user, I want to upload a file so that it is stored securely.

## Context
Files are uploaded via a multipart POST request.

## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, then the upload succeeds.
2. Given a duplicate upload, when submitted by the same user, then it is rejected gracefully.
3. Given a complete request, when all fields are present, then a successful response is returned.

## Non-Goals
1. Scanning file contents for viruses.
