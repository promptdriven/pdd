# verify

- Run the focused tests for the change and the repo's required checks.
- For a behavior fix, show that the new test fails on the old code in a throwaway copy, when you can.
- For a behavior fix, write `Proof (defect fixed):` and `Proof (gap closed):` with evidence for each in verify.md. Give a reason for each removed test or changed assertion.
- If only the warning light changed, write `Not fixed yet: this helps find the cause` in verify.md for pdd to lift to the PR top; use `Refs #N` and keep the issue open.
- Report the exact commands, exit codes and real output. Name what no test covers. Put the results first. Put the exact commands and long output last, in a closed `<details>` block.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
