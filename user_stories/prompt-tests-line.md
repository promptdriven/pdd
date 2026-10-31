# Read the Prompt tests line

I can paste the `Prompt tests` line that `pdd test` prints into my PR, and pdd still reads the `Runtime check` lines of my older PRs and saved results.

## Acceptance criteria

1. When the Story `place-order` passed, `pdd test --json` gives it the Story line "Prompt tests (place-order): …" and the total line "Prompt tests: …", and neither line says "Runtime check".
2. When the Stories `place-order` and `split-bill` both ran, `pdd test --json` gives each Story its own line, "Prompt tests (place-order): …" and "Prompt tests (split-bill): …", and the total line "Prompt tests: …", and no line says "Runtime check".

## What must not change

The rest of each line stays the same: the mark (✓, ✗, running, busy or no verdict), the criteria, checks and AI calls, ` (DRAFT)` and `(N for reruns)`. Exit codes, the table, report links and the other `--json` fields stay the same. pdd does not rewrite old PR bodies, saved run summaries or saved `--json` results.

## Rules to check

`pdd test` writes only the word `Prompt tests`: `Prompt tests (<story>): …` for each Story and `Prompt tests: …` for the total, in the text output and in each `summary_line`. The PR top lines that pdd writes say `Prompt tests (<story>): …` and `Prompt tests (all Stories): …`. Forbidden: a new line that says `Runtime check`.

Every reader accepts both words, and a `Prompt tests` line and an old `Runtime check` line count the same. The readers are the PR text that pdd builds from a step summary, `pdd workflow status` (`Stories: N of M Stories pass`), `pdd workflow view`, `pdd workflow evidence` with a saved `--json` result, and `pdd product status`. A saved result of pdd 0.1.12 with `"summary_line": "Runtime check (place-order): ✓ …"` still records with `pdd workflow evidence`. Forbidden: a reader that skips, miscounts or refuses a line only because it says `Runtime check`, or a verdict line that takes in the next `Prompt tests` line when the lines are joined with "; ".

The test file checks the lines that `pdd test --json` writes. The readers need saved runs, step summaries, PR bodies and GitHub replies, so the code area checks them with Node tests.
