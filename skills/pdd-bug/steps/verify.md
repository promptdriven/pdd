# verify

- Run replay and regression on the fix and a planted mistake (old code), per section 17 of RUNBOOK.md. Keep failures and tables. Code-only (§14): unchanged prompt passes both snapshots; native old fails for the bug, new passes. Crashes prove nothing.
- For an opted-in run, write replay-evidence.json in the run folder as section 17 specifies; the formal step updates its result.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Run nearby cases and the repo's required checks.
- Report commands, exits, real output and gaps.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- For a screen, run the local headless comparison in RUNBOOK §13. A Screen vs drawing table is mandatory in verify.md and the code PR; a missing part fails verify. Return to build on differences.

- Independently repeat the affected real behavior from a fresh checkout using `verification-setup.md` in the pdd-prompting skill. Report setup, native behavior, dependency scope and prompt-interpreter results separately; retain evidence outside the checkout.
