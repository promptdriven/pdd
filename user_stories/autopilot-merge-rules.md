As a repository operator, I want Autopilot to apply recorded merge rules and use
my base branch's GitHub merge queue, so that a change completes only after its
checks, merge result and independent audit are known.

## Acceptance criteria

1. Every refused merge names the failed rule. Missing evidence cannot pass.
2. A fresh review has no remaining must-fix. The full suite and required CI are
   green on the current head. At most two repairs are allowed. The area's
   autonomy, existing approval gates and human review requirements apply.
3. A queue on the actual base branch receives the checked head. A queued entry
   is pending. Queue failure cannot fall back to a direct merge.
4. Without a queue, the merge uses the exact checked head. Changed heads or
   bases and failed authorization comments prevent a write.
5. A confirmed merge waits for an independent audit of the merged commit.
   A failed or missing audit does not complete the change.

## Rules to check

For each of the six merge guards, missing or failing evidence prevents a merge
write. Repair counts 0, 1 and 2 can pass; 3 and malformed counts cannot pass.
Queue entry alone never completes the change.
