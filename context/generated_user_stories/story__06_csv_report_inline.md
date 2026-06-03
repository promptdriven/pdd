<!-- pdd-story-prompts: csv_report_python.prompt -->

# User Story: Csv Report Flow

## Covers

- Prompt behavior: Build a CSV report workflow.

## Story

As a prompt reviewer,
I want to verify that generated code can build a CSV report workflow,
so that the csv report prompt has reviewable behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `csv_report_python.prompt`: Build a CSV report workflow.

## Acceptance Criteria

1. Given `csv_report_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Build a CSV report workflow.
2. Given `csv_report_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Accept only .csv uploads with a header row.
3. Given `csv_report_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Return row_count and column_names in the summary.

## Oracle

- `csv_report_python.prompt` requires: Build a CSV report workflow.
- `csv_report_python.prompt` requires: Accept only .csv uploads with a header row.
- `csv_report_python.prompt` requires: Return row_count and column_names in the summary.

## Non-Oracle

These details should not matter:
- private helper names
- internal class structure
- exact wording of non-user-facing messages
- deterministic but irrelevant ordering

## Negative Cases

- MUST NOT log raw uploaded cell values.

## Non-Goals

- Private helper names, file organization, and internal refactors are out of scope unless the prompt explicitly requires them.
- New product behavior outside the linked prompt files is out of scope.

## Notes

- Generated deterministically from prompt content; edit this story when human review identifies missing acceptance criteria.
- `pdd detect --stories` should report no required prompt changes for this story before it is used as a prompt regression test.
