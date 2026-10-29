# Uninstall and restore the previous selection

As a tester, I can remove the development installation created from my checkout and return to the installation that was active before it.

## Acceptance criteria

1. Running the approved matching uninstall command removes the development version's managed record and restores the previously active version and state.
2. The command reports the restored active version and ends successfully.
3. If a different installation became active after the development install, uninstall reports the conflict and leaves the managed state unchanged.

## Rules to check

- Uninstall only removes the matching development installation; it must not delete an unrelated active version.
- A missing or repeated development uninstall is an error with no state change.
