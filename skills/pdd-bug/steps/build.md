# build

- Make the smallest change that meets the approved prompt, Story and cases.
- Add the regression test through the public interface. Never change a test to make it pass.
- Also write the replay test from section 17 of RUNBOOK.md (pdd-prompting skill). Never edit the Story's test file.
- If the fix needs a wider change, stop and explain.
- For a screen, read its linked `.ui.svg` as the layout spec; build its parts, words, order, ids and state. Follow RUNBOOK §13 and rebuild until the screen matches.

- In your `done` summary add the PR 2 fields of RUNBOOK §15: `Title:`, `Cause:`, `Fix:`, `Result:`, `Case:` rows and `File:` notes.
- Prepare and run the affected behavior using `verification-setup.md` in the pdd-prompting skill; keep any needed recipe and controlled fixtures in project source.
