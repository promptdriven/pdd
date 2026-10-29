# change

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 in the pdd-prompting skill. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/).
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Change only the approved scope. If a prompt owns it, read the pdd-prompting guide.md in full, change the prompt first, then code and a public-interface test.
- If you changed a prompt that has a test file, run `pdd check` on every Story of that prompt, as RUNBOOK.md says, before verify. Never send the same check on the same files again: to see its result, run `pdd check --read`. Keep its notes out of verify.md.
- After a ✗, read `Why:`/`Next:` and report; tell person kind, evidence fix. Follow RUNBOOK “After a ✗”; stop after 2. Show `Runtime check` and report link. Person decides expected values; the agent may propose, never make changes
