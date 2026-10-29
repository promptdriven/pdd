# verify

- Run the replay test and the regression test on the fix and on a planted mistake (here: the old code in a throwaway copy), as section 17 of RUNBOOK.md says. Keep the real failures. Write the table into verify.md.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Write code-replay.json in the run folder using RUNBOOK §17 and the original replay-baseline.json. Record every check and actual operation execution; missing or unmapped checks never pass.
- Run nearby cases and the repo's required checks.
- Report the exact commands, exit codes and real output, and what no test covers.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
