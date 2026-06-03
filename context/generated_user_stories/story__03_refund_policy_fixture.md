<!-- pdd-story-prompts: refund_policy_python.prompt -->

# User Story: Refund Policy Flow

## Covers

- R1: The system MUST approve a refund amount that is positive and less than or equal to the original charge amount.
- R2: The system MUST NOT approve a refund amount that exceeds the original charge amount.

## Story

As a prompt reviewer,
I want to verify that generated code can satisfy the system must approve a refund amount that is positive and less than or equal to the original charge amount. and the system must not approve a refund amount that exceeds the original charge amount.,
so that the refund policy prompt has reviewable behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `refund_policy_python.prompt`: <pdd-reason>Applies simple refund policy contract rules for generated-test traceability.</pdd-reason>

## Acceptance Criteria

1. Given `refund_policy_python.prompt` is the prompt under review, when R1 is exercised, then the system must approve a refund amount that is positive and less than or equal to the original charge amount. is satisfied: The system MUST approve a refund amount that is positive and less than or equal to the original charge amount.
2. Given `refund_policy_python.prompt` is the prompt under review, when R2 is exercised, then the system must not approve a refund amount that exceeds the original charge amount. is satisfied: The system MUST NOT approve a refund amount that exceeds the original charge amount.

## Oracle

- `refund_policy_python.prompt` R1: The system MUST approve a refund amount that is positive and less than or equal to the original charge amount.
- `refund_policy_python.prompt` R2: The system MUST NOT approve a refund amount that exceeds the original charge amount.

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering

## Negative Cases

- Approve a refund amount that exceeds the original charge amount.

## Non-Goals

- Private helper names, file organization, and internal refactors are out of scope unless the prompt explicitly requires them.
- New product behavior outside the linked prompt files is out of scope.

## Notes

- Generated deterministically from prompt content; edit this story when human review identifies missing acceptance criteria.
- `pdd detect --stories` should report no required prompt changes for this story before it is used as a prompt regression test.
