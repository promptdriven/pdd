# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: `*.prompt.md` Runtime block; Story tests: RUNBOOK §2 folder rules. The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md for behavioral-test guidance, and its story-guide.md in full before you write the Story.
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or about 10 moves/rows/calls; split replays; check expected state per part. Server limit: 10 minutes.
- Find the prompt that owns the behavior. Change it only if it is wrong or incomplete. If none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module.
- Write the Story in the person's words: the "As a …" line, the correct behavior and what must not change.
- For a page, check what it shows through its `render` operation (`{html}` and the facts it shows), with `count` or `equals`. It is never "browser-only, no PDD test".
- Test the issue input. Use requirement-based expected results, not code; write cases only for the issue's criteria.
- Put a precise rule and its forbidden result under `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines for a small change.
- For new prompts, recommend `pdd interface draft PROMPT` in a repo with at least one commit. Otherwise, write the Runtime block from the contract; fill its hash and lint.
