# User Story: Prompt lint upload sample

<!-- pdd-story-prompts: prompts/foo_python.prompt -->

## Story

As an upload API consumer,
I want duplicate uploads to be handled consistently,
so that retries do not create duplicate records.

## Acceptance Criteria

1. Given an authorized user, when they upload a valid file, then the upload succeeds.
2. Given a duplicate upload, when submitted by the same user, then it is rejected gracefully.
3. Given a complete request, when all fields are present, then a successful response is returned.
