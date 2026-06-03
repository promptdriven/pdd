<!-- pdd-story-prompts: foo_python.prompt, refund_python.prompt -->

# User Story: Refund and Foo Flow

## Covers

- prompts/refund_python.prompt#R1: Refund cap
- prompts/refund_python.prompt#R2: CRITICAL audit trail

## Story

As a prompt reviewer,
I want to verify that generated code can satisfy refund cap and critical audit trail,
so that the linked prompts have reviewable cross-module behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `refund_python.prompt`: <pdd-reason>Refund handler with contract obligations</pdd-reason>
- `foo_python.prompt`: <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>

## Acceptance Criteria

1. Given `refund_python.prompt` is the prompt under review, when R1 is exercised, then refund cap is satisfied: The system MUST cap refunds to the remaining balance.
2. Given `refund_python.prompt` is the prompt under review, when R2 is exercised, then critical audit trail is satisfied: The system MUST log every refund attempt.

## Oracle

- `refund_python.prompt` R1: The system MUST cap refunds to the remaining balance.
- `refund_python.prompt` R2: The system MUST log every refund attempt.

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering

## Negative Cases

- No prompt-specific forbidden outcomes were detected; preserve all explicit MUST NOT constraints when they are added.

## Non-Goals

- Private helper names, file organization, and internal refactors are out of scope unless the prompt explicitly requires them.
- New product behavior outside the linked prompt files is out of scope.

## Notes

- Generated deterministically from prompt content; edit this story when human review identifies missing acceptance criteria.
- `pdd detect --stories` should report no required prompt changes for this story before it is used as a prompt regression test.
