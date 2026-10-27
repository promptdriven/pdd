# build

- Build only the approved Story. The prompt is the source.
- Read the callers before you change a public interface.
- Test through the public interface. Never change a test to make it pass.
- Also write the replay test from section 17 of RUNBOOK.md (pdd-prompting skill). Never edit `tests/<story>.json`; if an expected value looks wrong, stop and ask the person.
