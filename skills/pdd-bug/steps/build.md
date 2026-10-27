# build

- Make the smallest change that meets the approved prompt, Story and cases.
- Add the regression test through the public interface. Never change a test to make it pass.
- Also write a replay test in the repo's test runner (e.g. `test/<story>.vectors.test.mjs`). It reads `tests/<story>.json` at run time and calls the real interface named by each step's `operation`, in order, with shared state.
- Never edit `tests/<story>.json`. If an expected value looks wrong, stop and ask the person: that is a PR 1 change.
- If the fix needs a wider change, stop and explain.
