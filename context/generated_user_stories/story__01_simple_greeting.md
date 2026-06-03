<!-- pdd-story-prompts: foo_python.prompt -->

# User Story: Foo Flow

## Covers

- Prompt behavior: <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>.

## Story

As a prompt reviewer,
I want to verify that generated code can <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>,
so that the foo prompt has reviewable behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `foo_python.prompt`: <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>

## Acceptance Criteria

1. Given `foo_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>.
2. Given `foo_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: <include>context/note.prompt</include>.
3. Given `foo_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: <shell>printf pdd-snapshot-demo-shell</shell>.

## Oracle

- `foo_python.prompt` requires: <pdd-reason>Test-plan prompt: preprocess with --snapshot (include + shell + web).</pdd-reason>.
- `foo_python.prompt` requires: <include>context/note.prompt</include>.
- `foo_python.prompt` requires: <shell>printf pdd-snapshot-demo-shell</shell>.

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
