# User Story: Upload file (cross-module ## Covers format)

<!-- pdd-story-prompts: valid_contract_python.prompt -->

## Story
As an authorized user, I want to upload a file so that it is stored securely.

## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, the server returns HTTP 201.
2. Given a duplicate upload, the server returns HTTP 409.

## Covers
- valid_contract_python.prompt#R1: duplicate upload rejection
- valid_contract_python.prompt#R2: authorized user check
- valid_contract_python.prompt#R3: HTTP 201 response

## Non-Goals
1. Virus scanning.
