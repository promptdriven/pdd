As an Autopilot operator, I want my machine's work to survive a restart without lost or repeated state, so that I can continue authorised work safely.

## Acceptance criteria

1. Existing launcher identity, pending work, local claim observations and run limits remain available after import and restart.
2. Clearing imported pending work prevents a retained old file from restoring that work.
3. Imported snapshots keep newer observations after restart. Retained old files stay unchanged.
4. Independent processes retain every committed call and cost row. Identical calls remain separate observations.
5. A failed transaction or a process killed before commit leaves the prior queue, local lease and event records together.
6. The machine run index remains usable with malformed old index data and keeps its existing selection limits.
7. Worker completion reads current coordinator state after migration. GitHub remains the shared authority for claims and dependency reviews.

## Native verification

Use the commands in [Autopilot machine storage](../docs/autopilot-storage.md).
The storage tests exercise the public adapters with temporary state and controlled
processes. The dependency tests use the repository's fake GitHub and Herdr.
No prompt-interpreter result is claimed. This Story needs review and approval.
