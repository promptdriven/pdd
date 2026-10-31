# check

For a Check ceiling, choose `--max-calls` of at least 3 times the worst-case estimate, including child calls and saved-data operations. Unused allowance is not charged.

If the pdd-prompting skill has a RUNBOOK.md, follow it. Run `pdd test` ONCE with no Story name, so all Stories are checked together. After fixing, re-check only the failing Stories by name. Never send the same check on the same files again: to see its result, run `pdd test --read`. In your `done` summary put only every `Prompt tests (<story>): …` line as pdd test prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Write your notes to `<run folder>/check.md`, never to verify.md. Otherwise review by hand, as the pdd-prompting SKILL.md and review.md say.

After a ✗, read `Why:`/`Next:`, the report step, criterion, prompt and test; tell the person the kind, evidence and proposed fix. Follow RUNBOOK “After a ✗”. After 2 fix rounds for the same ✗, stop and ask the person. A person decides expected values; the agent may propose a change, and never makes it.
