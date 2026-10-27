# change

- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 (in the pdd-prompting skill): prompts are `prompts/<name>.prompt.md` with a Runtime interface block; tests are `tests/<story>.json` in the runtime's test format. Copy its example.
- Change only the approved scope.
- If a prompt owns the changed behavior, read the pdd-prompting skill's guide.md in full. Change the prompt first, then the code.
- For a behavior change, add a test through the public interface. Take its expected result from the plan, not from the code.
- Keep existing tests unless the plan changes them. No unrelated refactors or new dependencies.
- If you changed a prompt that has a test file, run `pdd check` as the pdd-prompting skill's RUNBOOK.md says before verify. Keep its notes out of verify.md.
