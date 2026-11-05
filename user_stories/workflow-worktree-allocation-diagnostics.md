# Investigate intermittent worktree allocation failures

When two different issues allocate in separate processes, I expect both to get ready, isolated worktrees. If an allocation cannot be confirmed, I need enough safe evidence to investigate and the failed fixture preserved so I can distinguish possible resource pressure from shared Git contention. Not fixed yet: this helps find the cause; the issue stays open.

## Acceptance criteria

1. An unconfirmed new allocation after intent creation keeps the result envelope, null assignment and warning to inspect the same intent without repeating add or deleting work. Its message identifies the last attempted phase among run-file creation, run-file write/sync, issue claim/sync, Git add and reconciliation, or says unknown; it includes a safe native error code or numeric Git exit status when available, otherwise says unavailable.
2. If Git add fails or its reply is lost and reconciliation also fails, the diagnostic retains evidence of both. If reconciliation verifies the original identity, allocation is ready even after the add reply fails. Diagnostics omit raw error text, subprocess output, credentials and paths from errors, and do not claim a cause without evidence.
3. A failed separate-process fixture is preserved with its location and bounded phase/error and available resource and contention evidence. Missing evidence is reported as unknown. Both distinct issues still must be ready and isolated; no retry or cleanup destroys evidence of failure.

## Rules to check

An incomplete or uncertain intent never authorizes a second add, a new identity, deletion or automatic repair. A safe error is a native error code or numeric Git exit status, not arbitrary error text. Diagnostic evidence alone does not establish resource pressure or contention.

Interpreter scenario: NOT AVAILABLE. The owner has no executable Runtime interface binding native filesystem, UUID and separate-process effects. The native case inventory is in the external run notes; it describes required coverage, not an interpreter scenario or approval.
