# verify

- Run the replay test on the fix and on a planted mistake (here: the old code), as section 14 of RUNBOOK.md says. Write its table into verify.md.
- Run the regression test on the old code in a throwaway copy and keep its real failure. Then run it on the fix.
- Run nearby cases and the repo's required checks.
- Report the exact commands, exit codes and real output, and what no test covers.
