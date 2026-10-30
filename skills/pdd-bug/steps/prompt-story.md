# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: `*.prompt.md` with a Runtime interface block; the Story's test file, `tests/<story>.json` (RUNBOOK §2 names the folder when the repo already has tests/). The code area adds unit tests; PR 1 keeps main green.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or 10 moves/rows/calls; split replays with expected state. Limit: 10 minutes.
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write the Story in the person's words: the correct behavior and what must not change.
- For a page, check what it shows through its `render` operation (`{html}` and the facts it shows), with `count` or `equals`. It is never "browser-only, no PDD test".
- Keep the bug input as a case in the Story's test file, with its expected result from the requirement, not from the code. Write cases only for the issue's criteria.
- Put a precise rule (money, limits, permissions, state order) in the Story under `## Rules to check`, with its forbidden result.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines for a small change.
- Bind outside ports with supplied replies (RUNBOOK §21); preserve factories/methods with handles. Name unsupported native effects.
