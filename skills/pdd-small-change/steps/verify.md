# verify

- Update checklist state and evidence against the issue (RUNBOOK §15); run focused and required checks.
- Run `git diff --name-only` and `pdd owner`. If the diff touches `*.prompt.md`, `user_stories/*.md`, owned files or product/app code (`src/`, `app/`, etc.), add a line `Not checked: small-change touched owned or product code (<files>); pdd-bug or pdd-feature owns prompt and code behavior` in verify.md and a `File:` note in `done`.
- For a defect fix, test failure before the fix when possible, write `Proof (defect fixed):` and `Proof (gap closed):` in verify.md, and explain changed assertions.
- If warning-light only, write `Not fixed yet: this helps find the cause` in verify.md and use `Refs #N`.
- Put results and exit codes first; name uncovered gaps. Put the exact commands and long output last, in a closed `<details>` block.
- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.
- In `done` add RUNBOOK §15 fields (`Title:`, `Problem:`, `Change:`, `Result:`, `Case:`, `File:`); if needed run `pdd workflow prove ISSUE --test CMD --expect TEXT`.
