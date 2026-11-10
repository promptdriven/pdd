# verify

- Run replay on code and a planted mistake per section 17 of RUNBOOK.md. Write its table into verify.md, with one row group per Story.
- Opted-in runs: write replay-evidence.json (RUNBOOK §17); formal updates it.
- Put the tables first, after a `✗ N vectors fail` line if cases fail. Put the exact commands and long output last, in a closed `<details>` block.
- Run new cases, regression tests and `pdd workflow suite --command CMD`. Repeat real behavior via `verification-setup.md` and save `real-validation.json` in the run folder (`head`, fresh `verifier`, `recipe`, `oldCode`, `newCode`, `evidencePaths`).
- For a behavior fix, write `Proof (defect fixed):` and `Proof (gap closed):`, or `Not fixed yet: this helps find the cause` (`Refs #N`, issue open).
- Report exact commands, exits, real output and untested gaps.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- Screens: RUNBOOK §13 local headless comparison. A Screen vs drawing table is mandatory in verify.md and the code PR; missing parts fail verify; rebuild.
