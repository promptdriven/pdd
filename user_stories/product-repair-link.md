# Repair one broken run link

I can keep working on other planned runs and link a deleted issue again.

## Acceptance criteria

1. Status marks phone-1 unverified when its saved issue 81 is gone, while server-1 and barista-1 stay ready.
2. Next keeps server-1 and barista-1 ready despite the same invalid local run hint.
3. Preparing phone-1 again creates issue 82 after a complete empty search, starts no workflow and replaces the broken link.
