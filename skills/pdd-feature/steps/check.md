# check

For a Check ceiling, choose `--max-calls` of at least 3 times the worst-case estimate, including child calls and saved-data operations. Unused allowance is not charged.

If the pdd-prompting skill has a RUNBOOK.md, follow it. Run `pdd check` ONCE with no Story name, so all Stories are checked together. After fixing, re-check only the failing Stories by name. Never send the same check on the same files again: to see its result, run `pdd check --read`. Never change an expected value. In your `done` summary put only every `Runtime check (<story>): …` line as pdd check prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand, as the pdd-prompting SKILL.md and review.md say.
