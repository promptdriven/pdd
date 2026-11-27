# Both targets

Own `src/core/target-both.mjs`. `pdd test --target both` runs the same Story cases on the declared code and on the PDD interpreter, then reports every step and criterion where the two give different results. A difference means the prompt, as the interpreter reads it, and the code do not do the same thing on that input (#3296).

## Domain decisions

- **Why both.** `pdd test` shows the prompt meets the Story; `pdd test --target code` shows the code meets the same cases. Run separately, each reports pass or fail on its own and nobody sees that, on one input, the prompt says one thing and the code does another. Running both on the same vectors and matching the results check by check makes that visible.
- **Code first.** Run the code target first: it is local and makes no AI call. A selection error from it (exit 2) stops the command before the interpreter is called, so a typo never costs AI calls.
- **Interpreter run is an ordinary `pdd test`.** Call the runtime seam's `check` with the same Story words and `--json`. Pass on only `--fresh`, `--max-calls` and `--timeout`; the CLI rejects every other test option for this route. Unchanged passing Stories are reused from `.pdd/cache/test/` exactly as `pdd test` does, unless `--fresh`. Progress and plan lines from that run go to `stderr` as usual.
- **Matching checks.** Match by scenario file and step: the code report's step `scenario` against the interpreter row's `test`. Within a step, match each code check to the interpreter check with the same `step_id`, `criterion_id`, target (`result`) and `path`, in order when a step repeats one.
- **Interpreter values.** A failed interpreter check carries its actual value. A passed interpreter check is an `equals` check, so its value is the expected value. An interpreter row whose state is not `passed` or `failed` (refused, not run, busy, unknown) did not run any check; its reason is the row's `why`, else `reason` (a string, or the `message` of the `{code, message}` object that `pdd test --json` prints), else `note.message`.
- **Never agree by default.** A step the code did not run, or an interpreter row that did not run or was not reported, is `not compared` with the side and reason. It never counts as agreeing. A `failed` interpreter row must name every failed check: each `failed_checks` entry has a `step_id`, names a check of that code step (or a step the code did not run), and their number equals `checks.total - checks.passed` when the row gives those counts; an empty list never names them. Otherwise the row's checks that are not named as failed are `not compared` on the interpreter side with the reason `The interpreter reported failed but did not name every failed check` and the row's reason, never `passed`.

Each check lands in the first group whose condition holds, checked in this order:

| Order | Condition | Group |
|---|---|---|
| 1 | either side did not run it | not compared |
| 2 | one side passed and the other failed | disagree |
| 3 | both failed with different actual values (exact value comparison) | disagree |
| 4 | otherwise (both passed, or both failed with the same value) | agree |

A Story is `disagree` when any of its checks disagrees, otherwise `not compared` when anything in it was not compared or it has no compared check, otherwise `agree`. Interpreter rows for scenarios the code run did not select are reported in one extra entry with `story: null`, as not compared.

## Public contract

`runTargetBoth({root, words, options, json}, {stdout, stderr, env, check, codeTest})` is async and returns the exit code.

- `root` is the invocation working directory; `words` selects Stories as in `pdd test --target code`; `options` are the parsed test options; `json` selects JSON output.
- `codeTest` defaults to the compiled checker's `runCompiledTest`, called with `json: true` into a buffer; its `stderr` passes through. `check` defaults to the runtime seam's `check`, called with `{words, options, cwd: root}` and `{stdout: buffer, stderr, env}`.
- Exit 2 when the code run exits 2. Exit 3 when the code run prints no report. When the interpreter run prints no rows and exits with neither 0 nor 1, print the report (every check not compared) and return the interpreter's exit code, so a missing sign-in keeps its own code. Otherwise exit 0 only when the commit is known, at least one check was compared, nothing disagrees, nothing is not compared, and every Story passed on both targets; else exit 1.
- JSON output is one object: `target: "both"`, `commit`, `dirty` (both from the code report), `summary: {compared, agree, disagree, not_compared}` (`not_compared` counts entries in the Stories' `not_compared` lists), `interpreter: {exit_code, batch, calls, rows}` (`calls` sums row calls, or null when a row's count is unknown; `rows` is null when none were reported), and `stories`. Each Story has `story`, `status`, `code_status`, `interpreter_status` (the distinct interpreter states of its scenarios), `differing_steps` (`SCENARIO · STEP`), `differing_criteria`, `checks` and `not_compared`. Each check has `scenario`, `step_id`, `criterion_id`, `path`, `expected`, `group`, and `code` and `interpreter`, each `{status, actual}` or `{status: "not run", reason}`. Each `not_compared` item has `scenario`, `step_id`, `side` (`code` or `interpreter`), `reason`, and for a check also `criterion_id` and `path`.
- Text output starts with `Target both: N check(s) compared · D disagree · A agree · U not compared · C interpreter call(s)`, then one line per Story: its status in capitals, its path, and `(interpreter STATE, code STATUS)`. Under it, one line per disagreeing check, `SCENARIO · step STEP · CRITERION PATH: expected VALUE, interpreter VALUE, code VALUE`, where a passed side reads `as expected`; then one line per not-compared item ending `not compared: SIDE not run: REASON`. When the interpreter reported nothing, a last line says so with its exit code.
- Nothing is written to `.pdd` beyond what the two runs already save (`.pdd/code-test/latest.json`, the interpreter's batch and test cache).

## Dependencies

[Compiled Story checks](compiled-test.prompt.md) runs the code target and supplies the step `scenario`. [Runtime seam](runtime-seam.prompt.md#public-contract) supplies `check`, `exactValue` and `stringifyScenarioJson`.
