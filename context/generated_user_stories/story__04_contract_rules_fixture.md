<!-- pdd-story-prompts: contract_rules_python.prompt -->

# User Story: Contract Rules Flow

## Covers

- R1: Positive amount
- R2: Remaining balance
- R3: No provider call before validation

## Story

As a prompt reviewer,
I want to verify that generated code can satisfy positive amount, remaining balance, and no provider call before validation,
so that the contract rules prompt has reviewable behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `contract_rules_python.prompt`: Fixture prompt with contract rules for testing user story template covers and negative cases seeding.

## Acceptance Criteria

1. Given `contract_rules_python.prompt` is the prompt under review, when R1 is exercised, then positive amount is satisfied: For every refund request, the system MUST reject the request when the requested amount is less than or equal to zero.
2. Given `contract_rules_python.prompt` is the prompt under review, when R2 is exercised, then remaining balance is satisfied: For every refund request, the system MUST reject the request when the requested amount is greater than the remaining refundable amount.
3. Given `contract_rules_python.prompt` is the prompt under review, when R3 is exercised, then no provider call before validation is satisfied: The system MUST NOT call the payment provider for requests rejected by R1 or R2.

## Oracle

- `contract_rules_python.prompt` R1: For every refund request, the system MUST reject the request when the requested amount is less than or equal to zero.
- `contract_rules_python.prompt` R2: For every refund request, the system MUST reject the request when the requested amount is greater than the remaining refundable amount.
- `contract_rules_python.prompt` R3: The system MUST NOT call the payment provider for requests rejected by R1 or R2.

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering

## Negative Cases

- Call the payment provider for requests rejected by R1 or R2.

## Non-Goals

- Private helper names, file organization, and internal refactors are out of scope unless the prompt explicitly requires them.
- New product behavior outside the linked prompt files is out of scope.

## Notes

- Generated deterministically from prompt content; edit this story when human review identifies missing acceptance criteria.
- `pdd detect --stories` should report no required prompt changes for this story before it is used as a prompt regression test.
