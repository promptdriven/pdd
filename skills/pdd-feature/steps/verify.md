# verify

- Run the replay test on the code and on a planted mistake, as section 17 of RUNBOOK.md says. Write its table into verify.md, with one row group per Story.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Run the new cases, the regression tests and the repo's required checks.
- Report the exact commands, exit codes and real output. Name what no test covers.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- For a screen, run the local headless comparison in RUNBOOK §13. A Screen vs drawing table is mandatory in verify.md and PR 2; a missing part fails verify. Return to build on differences.
