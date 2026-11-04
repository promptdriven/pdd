# pdd's own results for a run

Own `src/workflow-results.mjs`. A person and a checker must tell which results pdd recorded and which ones an agent typed (#2904). This module reads pdd's own saved results for one workflow run. It reads files only: it never runs a test, calls the interpreter, changes a file or stops a command.

Export `readRunResults({root, runDir, runId, since}, {env, capture})`. It returns a list, in this order, of what it finds:

- `pdd test`: the newest saved check batch (`intent` `check`) in the runtime state folder (`PDD_STATE_DIR`, else `~/.pdd/runtime`, then `batches/<BATCH>/`) whose `batch.json` names the same real folder as `root` and whose `created_at` is at or after `since` (epoch ms). Its result is the `summary_line` of its `summary.json` and each distinct per-Story `summary_line` (else `result not saved (the check did not finish)`). `source` is `current` when `capture(root, {tests, appMap: null})` of the batch's selected tests gives the batch's `source_sha256`, `changed` when it differs, else `unknown`. `engine` is the first known row `engine_sha` (12 characters) and `model` the first known `requested_model`, when known.
- `pdd lint`: the newest saved lint batch (`intent` `lint-only`) under the same rules. Its result is `Lint: N of M tests pass. 0 AI calls.` when the lint ended, else `Lint: result unknown (the lint did not finish).`
- `pdd workflow prove`: `<runDir>/old-code-proof.json` when its `runId` is this run's, with `Old-code proof: OUTCOME`, the file time and its head.

Skip unreadable, foreign, malformed or older records without a warning. Batch names match `YYYYMMDD-HHMMSS-xxxx`. Clean each shown value to one line, and write `pdd-workflow:` inside it as `pdd-workflow\u003a`, so saved text never makes an ownership marker.

Export `resultLines(results, {kinds})`. Each result becomes one line that starts with `pdd result: `: `pdd result: KIND (batch B, ISO time, source S, engine E, model M, head H): RESULT[; STORY LINE…]`, leaving out unknown facts. `kinds` limits the kinds shown. With nothing to show, the one line is `noResultLine(kinds)`: `pdd result: none. pdd has no pdd test, pdd lint or pdd workflow prove result of its own for this run (pdd:no-verdict).`, naming only the selected kinds. Also export `PDD_RESULT` (`pdd result`) and `NO_VERDICT` (`pdd:no-verdict`).

## Dependencies

- [Runtime client](runtime-client.prompt.md): required context for the saved batch files (`batch.json`, `summary.json`) that `pdd test` and `pdd lint` write.
- [Preflight](runtime-preflight.prompt.md): required for `captureSource`, the default `capture`.
- [Old-code proof](workflow-prove.prompt.md): required context for `old-code-proof.json`.
