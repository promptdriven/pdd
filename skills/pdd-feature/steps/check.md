# check

If the pdd-prompting skill has a RUNBOOK.md, run `pdd check` on every Story as it says. If a Story fails, fix only the failing Stories (never an expected value) and check only those again. In your `done` summary put only every `Runtime check (<story>): …` line as pdd check prints it, then the overall `Runtime check: …` line, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand:
- Read the pdd-prompting SKILL.md and review.md. Review as review.md says.
- Trace a normal case and an important edge case through the prompt.
