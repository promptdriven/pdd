# reproduce

- Read the issue, repo rules and owning prompt.
- If the fix changes no product behavior and plans only unowned path d non-code files (docs, CI, lockfiles, non-behavior metadata or test maintenance — never `*.prompt.md` or `user_stories/*.md`): outside `pdd workflow run`, switch to pdd-small-change (no Story or prompt); in a run, report this so the main chat uses `<pdd> workflow ask` to start `pdd workflow run small-change N`.
- Find the smallest safe input for the bug; record setup, input, command, expected and actual.
- If a prompt owns this behavior, follow RUNBOOK.md section 14: write a test from the issue, run `pdd test` on the CURRENT prompt, report ✗ or ✓, and put its `Prompt tests` line(s) and the report link(s) in your `done` summary as the "before" report.
- If no prompt exists, say so plainly, in the words of section 14.
- Record `Defect:` and `Not caught because:` in reproduce.md; if not reproduced, say why and never guess.
- In `done` add `Problem:` and one `Case: INPUT | TODAY | EXPECTED` line per issue case (RUNBOOK §15).
- Bind outside dependencies per pdd-prompting RUNBOOK §21 with deterministic replies; keep factory/method handles and name unsupported native effects.
