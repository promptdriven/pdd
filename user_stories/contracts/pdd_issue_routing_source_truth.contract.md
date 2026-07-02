<!-- pdd-story-contract derived-from-story="../story__pdd_issue_routing_source_truth.md" story-hash="d583eb07cd71590d" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Issues route to the right workflow

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_issue_routing_source_truth.md`), not this contract.

## Covers

- R1: Routing policy classifies issue intent from the issue source, not from stale branch names or previous workflow state.
- R2: Feature requests route to change workflows.
- R3: Bug reports route to bug/fix workflows.
- R4: Test requests route to test-generation workflows.
- R5: Ambiguous routing produces a reviewable reason instead of silently choosing the wrong workflow.

## Context

Routing is the first unit-test-like assertion in every issue-driven workflow:
if PDD chooses the wrong workflow, later generated stories and tests are the
wrong evidence even if they pass locally.

## Acceptance Criteria

1. Given an issue describes new desired behavior, when routing runs, then PDD selects the change workflow.
2. Given an issue describes broken existing behavior, when routing runs, then PDD selects the bug/fix workflow.
3. Given an issue asks for coverage, tests, or validation, when routing runs, then PDD selects the test workflow.
4. Given branch names, labels, and previous comments conflict with the issue body, when routing runs, then the issue body remains the source of truth or the ambiguity is surfaced.
5. Given routing is ambiguous, when the workflow cannot choose safely, then it records a reason for human review instead of starting the wrong workflow.

## Oracle

These details matter for pass/fail:
- routing uses issue source truth
- feature, bug, and test requests map to distinct workflows
- ambiguous cases are surfaced
- previous workflow state does not override current issue intent silently
- selected orchestrator matches the chosen task type

## Non-Oracle

These details should not matter:
- exact wording of a routing explanation
- cosmetic labels on GitHub comments
- provider/model used after routing
- internal classifier implementation

## Negative Cases

- A bug report must not be routed to feature change because the branch name says change.
- A feature request must not be routed to bug fix because an old comment mentioned a failure.
- A test request must not create prompt changes before coverage requirements are understood.
- Ambiguity must not silently choose the most destructive workflow.

## Non-Goals

- This story does not require live GitHub labels.
- This story does not cover every issue template.
- This story does not prescribe the routing model prompt internals.

## Candidate Prompts

- `prompts/routing_policy_python.prompt` - owns routing policy behavior.
- `prompts/task_routing_csv.prompt` - records task routing categories.
- `prompts/agentic_change_orchestrator_python.prompt` - owns feature workflow orchestration.
- `prompts/agentic_bug_orchestrator_python.prompt` - owns bug workflow orchestration.
- `prompts/agentic_test_orchestrator_python.prompt` - owns test workflow orchestration.

## Notes

This story protects source-of-truth routing as a first-class regression oracle.
