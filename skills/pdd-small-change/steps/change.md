# change

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 in the pdd-prompting skill. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/).
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Change only the approved scope.
- If a prompt owns the changed behavior, read the pdd-prompting skill's guide.md in full. Change the prompt first, then the code.
- For a behavior change, add a test through the public interface. Take its expected result from the plan, not from the code.
- Keep existing tests unless the plan changes them. Make no unrelated refactors or new dependencies.
- If you changed a prompt that has a test file, run `pdd check` on every Story of that prompt, as RUNBOOK.md says, before verify. Never send the same check on the same files again: to see its result, run `pdd check --read`. Keep its notes out of verify.md.
- After a ✗, read `Why:`, `Next:` and the report. Tell the person the kind, the evidence and the proposed fix. Follow RUNBOOK “After a ✗”. After 2 fix rounds for the same ✗, stop and ask the person. In your `done` summary put the `Runtime check` line and the report link.
