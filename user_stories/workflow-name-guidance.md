# Name the workflow

I can see how to add the missing workflow name when I try to start work with only an issue number.

## Acceptance criteria

1. `pdd workflow run 81` prints "Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list." to stderr, prints nothing to stdout and exits with code 2.
