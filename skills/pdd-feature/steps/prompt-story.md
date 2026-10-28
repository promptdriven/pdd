# prompt-story

- First read the pdd-prompting skill's guide.md in full and its RUNBOOK.md §2–§4. Copy the RUNBOOK examples: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/). Runtime tests are not the repo's unit tests; the code area adds those, so merging PR 1 never turns main red.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Update the prompt that owns the behavior. Change one prompt when you can. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write every Story in `user_stories/PLAN.md`, each with its own test file. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. A page with no mockup gets a `render` operation that returns `{html}` and the facts it shows, checked with `count` or `equals` (such as `/emptyMessage`). It is never "browser-only, no runtime test".
- Write cases only for the issue's criteria. Put a precise rule (money, limits, permissions, state order) in the Story under `## Rules to check`, with its forbidden result.
- PR 1 holds only the prompt, the Story and its runtime test files, under about 200 lines for a small change.
