# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: `*.prompt.md` Runtime block; Story path `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/). The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or 10 moves/rows/calls; split replays with expected state. Limit: 10 minutes.
- Change it only if it is wrong or incomplete; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write the Story in the person's words ("As a …", right behavior, what must not change).
- For a page, check what it shows through its `render` operation (`{html}` and facts), with `count` or `equals`; never "browser-only, no PDD test".
- Test the issue input from requirements, not code; write cases only for the issue's criteria.
- Put precise rules in the Story under `## Rules to check`, with the forbidden result.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
- Draft `pdd interface draft PROMPT`; show lint/coverage. Case outside the declared interface: change the prompt and interface first (draft, `--refresh`/`--extend --contract FILE`), and ask a route question only when the prose cannot express the behavior.
