<!-- pdd-story-prompts: notify_python.prompt, upload_python.prompt -->

# User Story: Upload and Notify Flow

## Covers

- `upload_python.prompt`: Handle file uploads.
- `notify_python.prompt`: Send notifications when upload completes.

## Story

As a prompt reviewer,
I want to verify that generated code can handle file uploads; and send notifications when upload completes,
so that the linked prompts have reviewable cross-module behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `upload_python.prompt`: Handle file uploads.
- `notify_python.prompt`: Send notifications when upload completes.

## Acceptance Criteria

1. Given `upload_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Handle file uploads.
2. Given `upload_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Accept PDF and CSV files up to 10 MB.
3. Given `upload_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Return an upload_id on success.
4. Given `notify_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Send notifications when upload completes.
5. Given `notify_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Email the uploader with the upload_id.
6. Given `notify_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: MUST NOT send notifications for failed uploads.

## Oracle

- `upload_python.prompt` requires: Handle file uploads.
- `upload_python.prompt` requires: Accept PDF and CSV files up to 10 MB.
- `upload_python.prompt` requires: Return an upload_id on success.
- `notify_python.prompt` requires: Send notifications when upload completes.
- `notify_python.prompt` requires: Email the uploader with the upload_id.
- `notify_python.prompt` requires: MUST NOT send notifications for failed uploads.

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering

## Negative Cases

- MUST NOT send notifications for failed uploads.

## Non-Goals

- Private helper names, file organization, and internal refactors are out of scope unless the prompt explicitly requires them.
- New product behavior outside the linked prompt files is out of scope.

## Notes

- Generated deterministically from prompt content; edit this story when human review identifies missing acceptance criteria.
- `pdd detect --stories` should report no required prompt changes for this story before it is used as a prompt regression test.
