# Open the same workflow run consistently

As a person returning to my workflow, I can trust its saved chat state and reopen it through checkout aliases or stale layout records without losing the run or creating another agent.

## Acceptance criteria

1. A starting chat is saved before its first launch. Status and open keep it starting until confirmed; after the shared startup grace open says "starting, not confirmed" and offers the same open command. Missing observations never mean ended.
2. A confirmed native session makes the chat running. Only a positive pane exit or native session end makes it ended; a definite launch failure carries its code. Unknown inspection preserves custody, and positive end/failure evidence survives an unavailable inspection.
3. A checkout and its filesystem alias identify the same run in either direction. Separate clones remain separate even when their repository names match.
4. A missing or stale layout cache is rebuilt from the saved run and one verified matching live workspace. A missing chat tab can be reopened in that same run; repeated repair preserves peers and never closes or deletes a workspace or tab.
5. Unsafe or ambiguous repair keeps the run and reports the mismatching field, expected value and observed value. No repair creates another worktree, changes workflow progress or starts a fresh native session blindly.

## Rules to check

One run record owns chat lifecycle and identity. Index and layout caches cannot override it. Starting, running, ended, failed and unknown are explicit chat states, separate from workflow state. Startup waits use one shared 30-second grace and the saved request anchor. Cancellation at the final checkpoint prevents dispatch; late observations never resurrect it.

Runtime check: NOT RUN. The current Interpreter entries do not bind native Herdr inventories, filesystem identity, clock waits, session discovery or atomic run checkpoints. Deterministic native tests inject these boundaries; no remote check was requested.
