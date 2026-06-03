<!-- pdd-story-prompts: code_generator_python.prompt -->

# User Story: Code Generator Flow

## Covers

- Prompt behavior: <include>../context/python_preamble.prompt</include>.

## Story

As a prompt reviewer,
I want to verify that generated code can <include>../context/python_preamble.prompt</include>,
so that the code generator prompt has reviewable behavior before code generation.

## Context

Use the linked prompt files as the source of truth for behavior, fixtures, dependencies, external calls, records, and user-visible outcomes.
Each acceptance criterion below is derived from concrete prompt text so reviewers can treat this story as a prompt regression test.

This story covers the following prompt files:
- `code_generator_python.prompt`: <include>../context/python_preamble.prompt</include>

## Acceptance Criteria

1. Given `code_generator_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: <include>../context/python_preamble.prompt</include>.
2. Given `code_generator_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: Inputs:.
3. Given `code_generator_python.prompt` is used for generation, when the generated behavior is reviewed, then it implements: 'prompt' - A string containing the raw prompt to be processed.

## Oracle

- `code_generator_python.prompt` requires: <include>../context/python_preamble.prompt</include>.
- `code_generator_python.prompt` requires: Inputs:.
- `code_generator_python.prompt` requires: 'prompt' - A string containing the raw prompt to be processed.

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
