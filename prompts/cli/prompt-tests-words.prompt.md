# Prompt tests PR words

Own `src/prompt-tests-words.mjs`: the canonical PDD paste-line label and legacy-compatible reader pattern for PR bodies, workflow gates, saved run summaries, and read-only review. Pure module: no I/O or imports.

## Public contract

- Export `PROMPT_TESTS_LABEL = 'Prompt tests'`: the sole label written at the start of Story and overall paste lines (`Prompt tests (<story>): …` and `Prompt tests: …`). New output never writes `Runtime check`.
- Export `PROMPT_TESTS_WORDS = '(?:Prompt tests|Runtime check)'`: the regular-expression source used by workflow and review readers so `Prompt tests` lines and historical `Runtime check` lines in older PR bodies, saved run summaries, and saved `--json` results parse identically.

## Dependencies

None.

## Caller navigation

[`src/workflow-runner.mjs`](workflow-runner.prompt.md#prompt-tests-lines) and [`src/workflow-view.mjs`](workflow-view.prompt.md) import these constants to parse and normalize PR evidence lines; [`src/runtime-seam.mjs`](runtime-seam.prompt.md) re-exports them and supplies `PROMPT_TESTS_LABEL` as `promptTestsLabel` to [`src/runtime/runtime-output.mjs`](runtime-output.prompt.md#prompt-tests-line) and [`src/runtime/runtime-client.mjs`](runtime-client.prompt.md).

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"221edf3350be3e0713f6ae26221ebb81b75242c69ba9f85cc4a08c2d7388373e","reason":"Exports pure JavaScript string constants for PDD PR evidence labels and regular-expression patterns with no callable Runtime entry."}
```
</details>
