# User Story: Upload file (valid rule IDs in ## Covers)

<!-- pdd-story-prompts: valid_contract_python.prompt -->

## Story
As an authorized user, I want to upload a file so that it is stored securely.

## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, the server returns HTTP 201.
2. Given a duplicate upload, when submitted, the server returns HTTP 409.
3. Given an invalid file type, when uploaded, the server returns HTTP 422.

## Covers
- R1: duplicate upload rejection
- R2: authorized user check
- R3: HTTP 201 response

## Non-Goals
1. Virus scanning.
