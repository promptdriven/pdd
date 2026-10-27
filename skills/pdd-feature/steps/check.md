# check

If the pdd-prompting skill has a RUNBOOK.md, run `pdd check` on every Story as it says. If a Story fails, fix only the failing Stories (never an expected value) and check only those again. Put only pdd check's `Runtime check (<story>):` line and its `Report:` line for each Story, in PLAN.md order, then the overall `Runtime check:` and `Report:` lines, in your `done` summary, one per line. Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand:
- Read the pdd-prompting SKILL.md and review.md. Review as review.md says.
- Trace a normal case and an important edge case through the prompt.
