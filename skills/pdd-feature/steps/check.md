# check

Skip plain `pdd lint`; check `pdd-prompting/review.md` and run `pdd lint --codex <story> --issue <N>` (when Codex is available) to catch Story-Prompt mismatches and missed issue asks before `pdd test`.

Set `--max-calls` ≥3× worst-case calls (children/data included); unused is free.

If the pdd-prompting skill has a RUNBOOK.md, follow it. Run `pdd test` ONCE with no Story name, so all Stories are checked together. After fixing, re-check only the failing Stories by name. Never send the same check on the same files again: to see its result, run `pdd test --read`. In your `done` summary put every `Prompt tests (<story>): …` line as pdd test prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; ". After a re-check, keep the lines of the Stories that passed and replace the re-checked ones. Add the PR 1 fields of RUNBOOK §15. Write your notes to `<run folder>/check.md`, never to verify.md. Else follow pdd-prompting SKILL.md and review.md.

On ✗, read `Why:`/`Next:`, report step, criterion, prompt and test; tell the person kind, evidence and fix (RUNBOOK “After a ✗”). Ask after 2 rounds on one ✗. Propose expected-value edits for the card; undo on no.
