# prompt-story

- Read pdd-prompting's guide.md in full, story-guide.md in full and RUNBOOK.md (§2–§4 fast path). The code area adds unit tests; PR 1 keeps main green.
- `0` Runtime Stories applies only if no user-visible outcome changes or an existing Story checks the enclosing user flow; if native/crypto/I/O affects an uncovered user-visible flow, write/update the enclosing checkable flow prompt + `1` Story over an injected port (never link `kind: native-only` adapters under `## Dependencies`).
- Stay on RUNBOOK.md's fast path (do NOT open `runbook/*.md` or `review.md` unless hitting a named router edge case). Keep steps to 1 action or 10 moves/rows/calls; split replays with expected state. 10-minute limit.
- Find the behavior's prompt. Change it only if it is wrong or incomplete; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. State WHAT, WHY (`## Domain decisions`) and failure edges, never HOW; never minify JSON.
- Write the Story in the person's words: "As a …", the right behavior and what must not change.
- For a page, check what it shows through its `render` operation (`{html}` and facts), with `count` or `equals`, never "browser-only, no PDD test".
- Test the issue input with requirement-based expectations, not code; write cases only for the issue's criteria and run `pdd lint --local`.
- Put precise rules and forbidden results under `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
