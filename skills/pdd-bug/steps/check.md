# check

For a Check ceiling, choose `--max-calls` of at least 3 times the worst-case estimate, including child calls and saved-data operations. Unused allowance is not charged.

If the pdd-prompting skill has a RUNBOOK.md, run `pdd test` as it says, and show before ✗ → after ✓. Check every Story whose prompt changed, not only the bug's Story. Never send the same check on the same files again: to see its result, run `pdd test --read`. Start your `done` summary with two lines for the top of PR 1: the verdict line of RUNBOOK §14 for the "before" result, then `Before ✗ 0 of 1 criteria <report URL> → after ✓ 5 of 5 criteria <report URL>` with the real results (`Before: no prompt` when none existed). Then put pdd test's `Runtime check` line(s) and the report link(s). Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand:
- Read the pdd-prompting SKILL.md and review.md, and review as it says.
- Trace the bug input and one unaffected case through the prompt.
- Never accept the buggy output as the expectation.
