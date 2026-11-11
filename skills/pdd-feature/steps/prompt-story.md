# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: `*.prompt.md` Runtime block; Story tests: RUNBOOK §2 folder rules. The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md for tests.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Update the prompt that owns behavior. Never write a new Story or prompt for a docs, config, CI, package data or test file.
- When `pdd owner FILE` finds no prompt for a product file that you must change (source code that people maintain; not generated, vendored or lock files), first write its prompt from the current code, without asking: the file's whole behavior today (for a very large file, its public behavior: exports, inputs, outputs, errors). It starts as a draft. Then update it for the issue. List it in your `done` summary: `File: PROMPT — new, from the current code`.
- A new code file starts with the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write every Story in `user_stories/PLAN.md`, each with its own test file and "As a …" line. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. A page with no mockup gets a `render` operation that returns `{html}` and the facts it shows, checked with `count` or `equals` (such as `/emptyMessage`). It is never "browser-only, no PDD test".
- Write cases only for the issue's criteria. Put money, limit, permission or state rules under `## Rules to check`; state the forbidden result.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines for a small change, not counting a prompt written from the current code.
- For new prompts, recommend `pdd interface draft PROMPT` in a repo with at least one commit. Otherwise, write the Runtime block from the contract; fill its hash and lint.
