# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: `*.prompt.md` Runtime block; Story path `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/). The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or 10 moves/rows/calls; split replays with expected state. Limit: 10 minutes.
- Update the prompt that owns behavior (if none: the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module).
- Write every Story in `user_stories/PLAN.md`, each with its own test file and "As a …" line. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. With no mockup, a `render` operation that returns `{html}` and facts, checked with `count` or `equals` (`/emptyMessage`), never "browser-only, no PDD test".
- Write cases only for the issue's criteria. Put rules under `## Rules to check`, with the forbidden result.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
- Draft `pdd interface draft PROMPT`; show lint/coverage. Expected case outside the declared interface: widen prompt + interface first (draft, `--refresh`/`--extend --contract FILE`); ask a route question only if prose cannot express the behavior.
