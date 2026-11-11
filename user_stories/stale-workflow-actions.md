# Refuse stale workflow actions

As a person using a phone, I can act on a specific gate or step so that a late action cannot change a run that has moved on.

## Acceptance criteria

1. An action with the current gate or step works as before.
2. Approve, changes, cancel and open with a different expected gate or step refuse with exit code 6, name the current position and leave the run, approvals, chat and files unchanged.
