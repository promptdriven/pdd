# change

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 in the pdd-prompting skill. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/).
- Read pdd-prompting/review.md.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Complete the issue checklist (RUNBOOK §15); exclusions need issue authority.
- Read pdd-prompting's guide.md in full before you write a prompt. Change the prompt that owns a file before the file. New code starts with its prompt. Never write a new Story or prompt for a docs, config, CI, package data or test file.
- When `pdd owner FILE` finds no prompt for a product file that you must change (source code that people maintain; not generated, vendored or lock files), first write its prompt from the current code, without asking: the file's whole behavior today (for a very large file, its public behavior: exports, inputs, outputs, errors). It starts as a draft. List it in your `done` summary: `File: PROMPT — new, from the current code`.
- For a behavior change, add a test through the public interface. Take its expected result from the plan, not from the code. Owned code whose behavior changes also needs the pdd-bug evidence: a Story test, a replay test (RUNBOOK §17) and a Runtime line (its `pdd test` result). If that is too big, stop and suggest pdd-bug.
- Keep existing tests unless the plan changes them. No unrelated refactors/dependencies.
- If you changed a prompt that has a test file, run `pdd test` on every Story of that prompt, as RUNBOOK.md says, before verify. Never send the same check on the same files again: to see its result, run `pdd test --read`. Keep its notes out of verify.md.
- After a ✗, read `Why:`, `Next:` and the report. Tell the person the kind, the evidence and the proposed fix. Follow RUNBOOK “After a ✗”. After 2 fix rounds for the same ✗, stop and ask the person. In your `done` summary put the `Prompt tests` line and the report link.
