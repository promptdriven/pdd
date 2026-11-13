# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: Runtime block + §2 test folder. The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md and story-guide.md in full; apply scope triage (`0` Stories for internal/OS plumbing).
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or 10 moves/rows/calls; split replays with expected state. Limit: 10 minutes.
- Find the prompt for the behavior. Change it only if it is wrong or incomplete; if none exists, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. State WHAT, WHY (`## Domain decisions`) and failure edges, never HOW; let schema own fields; never minify JSON.
- Write the Story in the person's words: the "As a …" line, the correct behavior and what must not change.
- For a page, check what it shows through its `render` operation (`{html}` and facts), with `count` or `equals`, never "browser-only, no PDD test".
- Test the issue input with requirement-based expected results, not code; write cases only for the issue's criteria.
- Put a precise rule and its forbidden result under `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
- Recommend `pdd interface draft PROMPT` with at least one commit; otherwise write the Runtime block, fill hash and lint.
