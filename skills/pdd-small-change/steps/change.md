# change

- Before you write a prompt or a test file, read RUNBOOK.md and `runbook/files-and-runtime-block.md` (§2–§4) in the pdd-prompting skill. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/).
- Read pdd-prompting/review.md.
- From RUNBOOK.md, open only the 1–2 `runbook/` topic files that fit (skip unrelated files). Keep each step to one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Complete the issue checklist (RUNBOOK §15); exclusions need issue authority.
- Read pdd-prompting's guide.md in full before you write a prompt. Change the prompt that owns a file before the file. New code starts with its prompt. Files that no prompt owns change directly.
- For a behavior change, add a test through the public interface. Take its expected result from the plan, not from the code.
- Keep existing tests unless the plan changes them. No unrelated refactors/dependencies.
- If you changed a prompt that has a test file, run `pdd test` on every Story of that prompt, as RUNBOOK.md says, before verify. Never send the same check on the same files again: to see its result, run `pdd test --read`. Keep its notes out of verify.md.
- After a ✗, read `Why:`, `Next:` and the report. Tell the person the kind, the evidence and the proposed fix. Follow RUNBOOK “After a ✗”. After 2 fix rounds for the same ✗, stop and ask the person. In your `done` summary put the `Prompt tests` line and the report link.
