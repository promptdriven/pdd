# User Story: Upload file (unknown rule ID in ## Covers)

<!-- pdd-story-prompts: valid_contract_python.prompt -->

## Story
As an authorized user, I want to upload a file so that it is stored securely.

## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, the server returns HTTP 201.

## Covers
- R1: duplicate upload rejection
- R99: this rule does not exist

## Non-Goals
1. Virus scanning.
