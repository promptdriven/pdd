# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md §2–§4. Use RUNBOOK: Runtime block + §2 test folder. The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md and story-guide.md in full; apply scope triage (`0` Stories for internal/OS plumbing; ask before `> 3` Stories).
- Also read the RUNBOOK sections that fit: §6 CLI, §7 prompt calls, §9 money/dates, §13 screens; §8 check paths, §10 budgets (over cap: 0 calls). §18: one step = one action or 10 moves/rows/calls; split replays with expected state. Limit: 10 minutes.
- Update the prompt; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. State WHAT, WHY (`## Domain decisions`) and failure edges, never HOW; let schema own fields; never minify JSON.
- Write every Story in `user_stories/PLAN.md`, each with its own test file. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. Without a mockup, add a `render` operation that returns `{html}` and facts checked with `count` or `equals` (`/emptyMessage`), never "browser-only, no PDD test".
- Write cases only for the issue's criteria; put forbidden-result rules in `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
- Recommend `pdd interface draft PROMPT` with at least one commit; otherwise write the Runtime block, fill hash and lint.
