# verify

- Run replay and regression tests on the fix and old code in a throwaway copy (RUNBOOK §17). Keep real failures and write the table in verify.md.
- For opted-in runs, write replay-evidence.json (RUNBOOK §17); formal updates it.
- Put tables first, after `✗ N vectors fail` if cases fail; put commands and long output last in closed `<details>`.
- Record `Proof (defect fixed):` and `Proof (gap closed):` with evidence, or `Not fixed yet:` when the defect remains. Run `pdd workflow prove ISSUE --test COMMAND --expect TEXT` for recorded old-code proof.
- Run nearby cases and the repo's required checks.
- Report commands, exit codes, real output and coverage gaps.
- verify.md contains no local absolute paths or raw logs.
- For a screen, run the local headless comparison in RUNBOOK §13. A Screen vs drawing table is mandatory in verify.md and the code PR; a missing part fails verify. Return to build on differences.

- Independently repeat the affected real behavior from a fresh checkout using `verification-setup.md` in the pdd-prompting skill. Report setup, native behavior, dependency scope and prompt-interpreter results separately; retain evidence outside the checkout.
