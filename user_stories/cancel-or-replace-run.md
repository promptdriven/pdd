# Cancel a run or switch workflows

I can safely free an issue from the wrong workflow and see exactly how to continue or switch.

Issues: https://github.com/promptdriven/pdd/issues/2445 and https://github.com/promptdriven/pdd/issues/2446

## Acceptance criteria

1. I can decline cancellation or replacement before any agent stops, record changes, claim release or new run.
2. Cancelling a run by its ID asks first, confirms its live agent stopped, saves cancelled state for the phone and releases only its claim while preserving its worktree, branch, journal, artifacts and every PR without pushing.
3. After I confirm replacement of the current holder, it becomes cancelled before its claim is released and a distinct workflow run starts with new worktree and branch; the old work remains readable.
4. A replacement naming another run refuses before confirmation or effects, and never cancels the current holder or the other run.
5. An already-assigned issue refusal identifies the holder ID, workflow, step or stage, state and age, and shows current-alpha status, open and applicable approve commands plus the exact requested replacement command.
6. A scope recommendation to use feature stays with its reason, and both its approval gate and the holding-run refusal show it with the exact feature replacement command without switching automatically.
7. Existing issue-reference cancellation still works, and an already-cancelled run or a delayed completion cannot cancel again or change the replacement.

## Rules to check

The order is confirmation, confirmed agent stop or absence, durable cancelled record, release of the matching claim, then replacement allocation. Any missing confirmation or uncertain stop forbids release and replacement. Preserve every PR and all work. A wrong replacement ID forbids cancellation. Scope advice is retained and displayed; it never authorizes a switch. Keep alpha issue-reference commands; no obsolete resume/decision command is offered.

The runtime checks the runner contract using simulated production dependencies. Real filesystem durability, process stopping, concurrency and GitHub effects require code verification.

Code verification must run the public runner with real temporary run files and an isolated issue claim. Check status.json and index/C3 cancelled state, journal updates, exact preservation of all other saved fields and worktree/branch/journal/artifact contents, no pushes or PR closures, stop-before-release ordering, replacement identity, and delayed done from the old worktree. Runtime records.save assertions inspect the writeRun input ledger; they do not stand for those real-store checks.
