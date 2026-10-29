# Name the workflow

I can see how to add the missing workflow name when I try to start work with only an issue number.

## Acceptance criteria

1. `pdd workflow run 81` prints "Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list." to stderr, prints nothing to stdout and exits with code 2.

## What must not change

Other commands, workflow names, issue forms, help and option validation keep
their existing behavior. This usage error must not start a workflow.

## Rules to check

A positive decimal issue number in the workflow-name position must be rejected
as a usage error with guidance that repeats that number. Starting a workflow or
silently selecting a workflow is forbidden. The issue case is `81`; other command
behavior is a preservation boundary, not an additional behavior change.
