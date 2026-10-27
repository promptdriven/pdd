# build

- Build only the approved Story. The prompt is the source.
- Read the callers before you change a public interface.
- Test through the public interface. Never change a test to make it pass.
- Also write a replay test in the repo's test runner (e.g. `test/<story>.vectors.test.mjs`). It reads `tests/<story>.json` at run time and calls the real interface named by each step's `operation`, in order, with shared state.
- Never edit `tests/<story>.json`. If an expected value looks wrong, stop and ask the person: that is a PR 1 change.
