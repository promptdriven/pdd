# verify

- Run replay and regression tests on the fix and a planted mistake (old code), as section 17 of RUNBOOK.md says. Keep failures; write the table in verify.md.
- For opted-in runs, write replay-evidence.json (RUNBOOK §17); formal updates it.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Record `Proof (defect fixed):` and `Proof (gap closed):` or `Not fixed yet:` if unfixed. Run `pdd workflow prove ISSUE --test COMMAND --expect TEXT` for old-code proof.
- Run nearby cases and required checks. Report commands, exit codes, real output and coverage gaps.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- For a screen, run RUNBOOK §13's local headless comparison. A Screen vs drawing table is mandatory in verify.md and the code PR; a missing part fails verify. Return to build on differences.
- Independently repeat real behavior from a fresh checkout using `verification-setup.md` in the pdd-prompting skill. Report setup, native behavior, dependency scope and prompt-interpreter results separately; retain evidence outside the checkout.
