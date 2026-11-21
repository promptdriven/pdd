# prompt-story

- Read pdd-prompting's guide.md in full, story-guide.md in full and RUNBOOK.md (§2–§4, `review.md`). The code area adds unit tests; PR 1 keeps main green.
- Use `0` Stories + one `"No Story:"` PR line for internal changes, edit the existing Story when fixing an existing user slice, or write `1` Story for an uncovered user-visible loop over an injected port (never link `kind: native-only` adapters under `## Dependencies`).
- Follow RUNBOOK.md budgets: keep steps to 1 action or 10 moves/rows/calls; split replays with expected state. 10-minute limit.
- Find the behavior's prompt. Change it only if it is wrong or incomplete; if none, write the SMALLEST prompt that owns only the issue's behavior (one function or one endpoint; a CLI has one program prompt), not the whole module. Put technical invariants and edge bounds in `## Domain decisions`, never HOW; never minify JSON.
- Write or update the Story in the person's words: "As a …", the right behavior and what must not change.
- For a page, check `render` / `handle_event` (and pure `apply` state rules) with exact `result` and `html_*` checks (no `app-map.json` required)—never "browser-only, no PDD test".
- Test the issue input with requirement-based expectations (`1` observable check per material claim), write cases only for the issue's criteria, and run `pdd files`, `pdd lint --local`, plus `pdd lint --codex <story> --issue <N>` (if Codex is available) to catch alignment or coverage gaps.
- Put user-visible forbidden outcomes under `## Rules to check`.
- PR 1 holds only the prompt, the Story and its PDD test files, under about 200 lines.
