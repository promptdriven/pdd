# Prompt tests PR words

Own `src/prompt-tests-words.mjs`: the canonical PDD paste-line label and legacy-compatible reader pattern for PR bodies, workflow gates, saved run summaries, and read-only review. Pure module: no I/O or imports.

## Public contract

- Export `PROMPT_TESTS_LABEL = 'Prompt tests'`: the sole label written at the start of Story and overall paste lines (`Prompt tests (<story>): …` and `Prompt tests: …`). New output never writes `Runtime check`.
- Export `PROMPT_TESTS_WORDS = '(?:Prompt tests|Runtime check)'`: the regular-expression source used by workflow and review readers so `Prompt tests` lines and historical `Runtime check` lines in older PR bodies, saved run summaries, and saved `--json` results parse identically.

## Dependencies

None.

## Caller navigation

[Workflow runner](workflow-runner.prompt.md#prompt-tests-lines) and [Workflow view](workflow-view.prompt.md) import these constants to parse and normalize PR evidence lines; [PDD to Runtime seam](runtime-seam.prompt.md) re-exports them and supplies `PROMPT_TESTS_LABEL` as `promptTestsLabel` to [Runtime output](runtime-output.prompt.md#prompt-tests-line) and [Runtime client](runtime-client.prompt.md).

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"draft","prose_sha256":"a4da9db9ae844f1cbd7882096924dc35ac82fde431c06056131d67465e46e184","reason":"Exports pure JavaScript string constants for PDD PR evidence labels and regular-expression patterns with no callable Runtime entry."}
```
</details>
