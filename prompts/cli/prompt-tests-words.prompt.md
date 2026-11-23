# Prompt tests PR words

Own `src/prompt-tests-words.mjs`: the canonical PDD paste-line label and legacy-compatible reader pattern for PR bodies, workflow gates, saved run summaries, and read-only review. Pure module: no I/O or imports.

## Public contract

- Export `PROMPT_TESTS_LABEL = 'Prompt tests'`: the sole label written at the start of Story and overall paste lines (`Prompt tests (<story>): …` and `Prompt tests: …`). New output never writes `Runtime check`.
- Export `PROMPT_TESTS_WORDS = '(?:Prompt tests|Runtime check)'`: the regular-expression source used by workflow and review readers so `Prompt tests` lines and historical `Runtime check` lines in older PR bodies, saved run summaries, and saved `--json` results parse identically.

## Dependencies

None.

## Caller navigation

Workflow runner and Workflow view import these constants to parse and normalize PR evidence lines; [PDD to Runtime seam](runtime-seam.prompt.md) re-exports them and supplies `PROMPT_TESTS_LABEL` as `promptTestsLabel` to `@promptdriven/runtime-client`.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256":"13525161d12f8da1de9bcc9d4e9a1b3cf9077679e0f569e4e01ceb61fc4c105e","reason":"Exports pure JavaScript string constants for PDD PR evidence labels and regular-expression patterns with no callable Runtime entry."}
```
</details>
