# prompt-story

- Read pdd-prompting's guide.md in full and its RUNBOOK.md router, then open `runbook/files-and-runtime-block.md` (§2–§4: files). The code area adds unit tests; PR 1 keeps main green.
- Read pdd-prompting/review.md and story-guide.md in full; ask before `> 3` Stories; `0` Runtime Stories applies only if no user-visible outcome changes or an existing Story checks the enclosing flow; if native/crypto/I/O affects an uncovered user flow, write/update its enclosing flow prompt + `1` Story over an injected port (plus any `kind: native-only` adapter).
- From RUNBOOK.md, open only the 1–2 `runbook/` topic files that fit (skip unrelated ones). Keep steps to 1 action or 10 moves/rows/calls; split replays with expected state. 10-minute limit.
- Update the prompt; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. State WHAT, WHY (`## Domain decisions`) and failure edges, never HOW; let schema own fields; never minify JSON.
- Write every Story in `user_stories/PLAN.md`, each with its own test file. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. Without a mockup, add a `render` operation that returns `{html}` and facts checked with `count` or `equals` (`/emptyMessage`), never "browser-only, no PDD test".
- Write cases only for the issue's criteria; put forbidden results in `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
