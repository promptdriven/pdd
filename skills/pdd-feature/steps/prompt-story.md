# prompt-story

- Read pdd-prompting's guide.md in full, story-guide.md in full and RUNBOOK.md (§2–§4, opening matching `runbook/*.md` files when needed). The code area adds unit tests; PR 1 keeps main green.
- Confirm broad multi-Story splits first; use `0` Stories + `"No Story:"` for internal changes, edit the existing Story when changing an existing slice, or write `1` Story per cohesive standalone user loop (never link `kind: native-only` adapters under `## Dependencies`).
- Follow RUNBOOK.md budgets: keep steps to 1 action or 10 moves/rows/calls; split replays with expected state. 10-minute limit.
- Update the prompt; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. Put technical invariants and edge bounds in `## Domain decisions`, never HOW; never minify JSON.
- Write every Story in `user_stories/PLAN.md`, each with its own test file. Exact data (seeds, long boards) goes in the tests; the Story says it in plain words.
- A page or a screen gets an app map, so the person can try it on the Screen. Without a mockup, add a `render` operation that returns `{html}` and facts checked with `count` or `equals` (`/emptyMessage`), never "browser-only, no PDD test".
- Write cases only for the issue's criteria (`1` observable check per claim; use `pdd calc` + `"derivation"`, no scratch scripts), put forbidden outcomes in `## Rules to check`, and run `pdd files` + `pdd lint --local`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
