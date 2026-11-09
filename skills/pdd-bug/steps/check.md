# check

Set `--max-calls` at least 3 times worst-case calls, including children and saved-data work. Unused allowance is free.

If the pdd-prompting skill has a RUNBOOK.md, follow §14. Code-only: unchanged ✓ → ✓, native old-fail/new-pass proof in PR body. Check every Story whose prompt changed, not only the bug's Story. Never send the same check on the same files again: to see its result, run `pdd test --read`. Prompt bug before ✗ → after ✓: Start your `done` summary with two lines for the top of PR 1: the verdict line of RUNBOOK §14 for the "before" result, then `Before ✗ 0 of 1 criteria <report URL> → after ✓ 5 of 5 criteria <report URL>` with the real results (`Before: no prompt` when none existed). Then put pdd test's `Prompt tests` line(s) and the report link(s). Then add the PR 1 fields of RUNBOOK §15. Write your notes to `<run folder>/check.md`, never to verify.md. Else review by hand:
- Read the pdd-prompting SKILL.md and review.md, and review as it says.
- Trace the bug input and one unaffected case through the prompt.
- Never accept the buggy output as the expectation.
- A person decides expected values: propose Story or value changes; run done to show the card. Undo it on no.
