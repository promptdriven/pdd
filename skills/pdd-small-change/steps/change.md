# change

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 in the pdd-prompting skill. Copy the RUNBOOK examples (`*.prompt.md` with a Runtime interface block, `tests/<story>.json`).
- Also read the RUNBOOK sections that fit: §6 a CLI, §7 a prompt that calls another, §9 money and dates, §13 a page or screen. For tests: §8 check paths, §10 the AI-call budget (over it, a test is refused at 0 calls), §18 ONE call for a whole move list, never 30 in a row.
- Change only the approved scope.
- If a prompt owns the changed behavior, read the pdd-prompting skill's guide.md in full. Change the prompt first, then the code.
- For a behavior change, add a test through the public interface. Take its expected result from the plan, not from the code.
- Keep existing tests unless the plan changes them. No unrelated refactors or new dependencies.
- If you changed a prompt that has a test file, run `pdd check` on every Story of that prompt, as the pdd-prompting skill's RUNBOOK.md says, before verify. Never send the same check on the same files again: to see its result, run `pdd check --read`. Keep its notes out of verify.md.
