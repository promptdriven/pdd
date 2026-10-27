# check

If the pdd-prompting skill has a RUNBOOK.md, follow it. Run `pdd check` ONCE with no Story name, so all Stories are checked together, and paste its per-Story lines. After fixing, re-check only the failing Stories by name. Never change an expected value. In your `done` summary put only every `Runtime check (<story>): …` line as pdd check prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand:
- Read the pdd-prompting SKILL.md and review.md, and review as it says.
- Trace a normal case and an important edge case through the prompt.
