# verify

- Run replay/regression on fix and planted mistake (old code), per section 17 of RUNBOOK.md; keep failure tables. Code-only (§14): unchanged prompt passes both snapshots; native old fails for the bug, new passes. Crashes prove nothing.
- Opted-in runs: write replay-evidence.json (RUNBOOK §17); formal updates it.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Record `Proof (defect fixed):` and `Proof (gap closed):` or `Not fixed yet:`. Run `pdd workflow prove ISSUE --test COMMAND --expect TEXT` for old-code proof.
- Run nearby/required checks. Report commands, exits, real output and gaps.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- Screens: RUNBOOK §13 local headless comparison. A Screen vs drawing table is mandatory in verify.md and the code PR; missing parts fail verify; rebuild.
- Independently repeat real behavior in a fresh checkout using `verification-setup.md` (pdd-prompting). Report setup, native behavior, dependency scope and prompt-interpreter results separately; retain evidence outside the checkout.
