# Understand a changed Herdr layout

I can see which saved Herdr workspace no longer matches my run and what to inspect before I retry.

## Acceptance criteria

1. When my saved workspace no longer matches, the error identifies its workspace ID, the mismatched field, and the expected and found values, while keeping `herdr_layout_identity_changed`.
2. Missing metadata and changed root identities give a specific field; an ambiguous pane count states the expected and found counts. If several fields differ, one deterministic first mismatch is reported.
3. Values with quotes, line breaks or control characters are safely quoted on one bounded line; a missing value says `missing`.
4. The message tells me to inspect the workspace in Herdr session `pdd`, restore its expected identity and retry my command; a lost original identity requires manual inspection, without an invented repair command.
5. I see the same diagnostic when opening a chat, starting the next area after approval, or receiving a workspace cleanup warning. The refusal performs no automatic repair or reallocation and preserves the worktree and saved ownership.

One-minute manual check: with a disposable run and stub Herdr, change its reported checkout path, open its area, then inspect the named workspace and expected/found path in the error. Restore the fixture and repeat with a missing metadata field and an extra root pane during cleanup. No provider or live Herdr session is needed.
