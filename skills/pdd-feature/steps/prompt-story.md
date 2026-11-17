# prompt-story

- Read pdd-prompting's guide.md in full, story-guide.md in full and RUNBOOK.md (§2–§4 fast path). The code area adds unit tests; PR 1 keeps main green.
- Ask before `> 3` Stories; `0` Runtime Stories applies only if no user-visible outcome changes or an existing Story checks the enclosing flow; if native/crypto/I/O affects an uncovered user flow, write/update its enclosing checkable prompt + `1` Story over an injected port (never link `kind: native-only` adapters under `## Dependencies`).
- Stay on RUNBOOK.md's fast path (do NOT open `runbook/*.md` or `review.md` unless hitting a router edge case). Keep steps to 1 action or 10 moves/rows/calls; split replays with expected state. 10-minute limit.
- Update the prompt; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. State WHAT, WHY (`## Domain decisions`) and failure edges, never HOW; never minify JSON.
- Write every Story in `user_stories/PLAN.md`, each with its own test file. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. Without a mockup, add a `render` operation that returns `{html}` and facts checked with `count` or `equals` (`/emptyMessage`), never "browser-only, no PDD test".
- Write cases only for the issue's criteria, put forbidden results in `## Rules to check`, and run `pdd files` (paired Stories/tests) + `pdd lint --local`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
