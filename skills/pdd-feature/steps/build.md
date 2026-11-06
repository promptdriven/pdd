# build

- Build the approved Stories in PLAN.md order. The prompt is the source.
- Read the callers before you change a public interface.
- Test through the public interface. Never change a test to make it pass.
- Write a replay test for each Story, as section 17 of RUNBOOK.md (pdd-prompting skill) says. Never edit the Story's test file.
- For a screen, read its linked `.ui.svg` as the layout spec; build its parts, words, order, ids and state. Follow RUNBOOK §13 and rebuild until the screen matches.

- Prepare and run the affected behavior using `verification-setup.md` in the pdd-prompting skill; keep any needed recipe and controlled fixtures in project source.
