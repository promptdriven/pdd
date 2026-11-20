# check

Skip plain `pdd lint`; check `pdd-prompting/review.md` and run `pdd lint --codex <story> --issue <N>` (when Codex is available) to catch Story-Prompt mismatches and missed issue asks before `pdd test`.

Set `--max-calls` ≥3× worst-case calls (children/data); unused is free.

If the pdd-prompting skill has a RUNBOOK.md, follow §14. Code-only: ✓ → ✓ + native proof in PR. Check every Story whose prompt changed, not only the bug's Story. Never send the same check on the same files again: to see its result, run `pdd test --read`. Prompt bug before ✗ → after ✓: Start your `done` summary with two lines for the top of PR 1: the verdict line of RUNBOOK §14 for the "before" result, then `Before ✗ 0 of 1 criteria <report URL> → after ✓ 5 of 5 criteria <report URL>` with the real results (`Before: no prompt` when none existed). Then put pdd test's `Prompt tests` line(s) and the report link(s). Add PR 1 fields of RUNBOOK §15. Write your notes to `<run folder>/check.md`, never to verify.md. Else review by hand:
- Follow pdd-prompting SKILL.md & review.md; trace bug + unaffected cases; never accept buggy output.
- Propose expected-value edits for the card; undo on no.
