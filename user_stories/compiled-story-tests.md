# Run Story tests on code

As a developer, I want to run my Story's approved cases on its real command-line implementation so that I can see whether the code matches them.

## Acceptance criteria

1. A command receives the case arguments and input and its exit code and output are checked against the Story.
2. A step that cannot run is reported as not run, and the Story does not pass.
3. Each Story result records the commit without an AI call.

## Rules to check

A step with an unsupported input, entry binding, expected error or check never
passes, and its Story never passes. A Story with an omitted or changed acceptance
criterion never passes.
