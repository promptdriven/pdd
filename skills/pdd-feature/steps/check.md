# check

Do not run `pdd lint` before `pdd test`; test includes lint.

Set `--max-calls` ≥3 times worst-case calls (children/saved-data included); unused is free.

If the pdd-prompting skill has a RUNBOOK.md, follow it. Run `pdd test` ONCE with no Story name, so all Stories are checked together. After fixing, re-check only the failing Stories by name. Never send the same check on the same files again: to see its result, run `pdd test --read`. In your `done` summary put every `Prompt tests (<story>): …` line as pdd test prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Add the PR 1 fields of RUNBOOK §15. Write your notes to `<run folder>/check.md`, never to verify.md. Else follow pdd-prompting SKILL.md and review.md.

After a ✗, read `Why:`/`Next:`, the report step, criterion, prompt and test; tell the person the kind, evidence and fix. Follow RUNBOOK “After a ✗”. After 2 fix rounds for the same ✗, stop and ask the person. A person decides expected values: write the proposed Story or value change, run done again; pdd shows it on the card. Undo it on no.
