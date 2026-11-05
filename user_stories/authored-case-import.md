# Save once to the exact original test or keep the case safely

I can receive a new case and keep both it and my authored work. A safe append reaches the exact original test. If a target, writer or starting world prevents this, I can recover the case without a false saved message.

Draft for review. These choices and expected results are not approved.

## Acceptance criteria

1. When a Story has two tests, an eligible received case appends once to the exact original selected test and leaves the other test byte for byte unchanged.
2. An append preserves authored metadata, criteria, initial data, simulation, context, every prior step, input, check and expected value, and all other bytes promised by the existing append contract.
3. Missing, changed, invalid, excluded, unsafe or ambiguous targets and incompatible starting worlds retain the full received case as pending or conflict with a reason and recovery location; no substitute original is chosen.
4. Under supported exclusive writer ownership, two savers keep both distinct cases once; without an editor handoff, the case stays pending and authored bytes stay unchanged.
5. An identical committed import is a no-op after restart; reused identity with different payload retains both as conflict, and later deliberate removal is not silently undone.
6. Interruption during receipt, preparation, publication, ledger update or recovery leaves complete authored JSON and the received case recoverable; restart establishes applied once or pending or conflict.
7. Terminal and MCP saves retain original association and confirmed starting data; an explicit isolated variant never rewrites original setup or pretends to satisfy an incompatible requested append.

## Rules to check

Proposed supported model: cooperating PDD savers and supported editor leases on local filesystems, or explicit closed-editor handoff. Unknown ownership stages durably. Atomic rename plus a final comparison cannot protect against an arbitrary non-cooperating editor. Forbidden: losing authored edits or the received case, treating a fetched or handled ID as a completed append, changing expectations, first-match fallback, or inventing reset steps. These are review choices, not existing guarantees.
