# Check selected scenario steps

As a developer iterating on a prompt, I want to check selected scenario steps, so that I can investigate a problem without running the whole Story.

## Acceptance criteria

1. A JSON result for a diagnostic check of step `late` marks it as a diagnostic subset and names `late` as the selected step.

## What must not change

- A diagnostic check leaves the authored Story and scenario files unchanged and does not replace a whole-Story pass.
- A full Story check continues to use all its steps.

## Rules to check

- An unknown step is refused before upload and available step IDs are shown.
- A selected step that needs an omitted predecessor is refused before upload.
- A diagnostic result cannot certify a Story, authorize approval or supply a merge verdict, including through a saved read.
