# understand

- Read the issue, repo rules and related code.
- With a product plan, read `product/map.md`, `product/plan.md` and named contracts first; prefix Story files with map IDs (`P01-menu.md`) and propose a plan PR rather than editing `contracts/`.
- State the wanted result, what must not change and out-of-scope items; separate decisions, current code and open questions.
- If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise.
- Scope triage: Stories are strictly for 1-minute user-observable behavior. Route internal harnesses, byte codecs and OS/fsync plumbing to `"kind": "native-only"` + deterministic `node --test` (`0` Runtime Stories).
- Count the separate behaviors. With 1 behavior, write one Story and no plan. With 2 or 3, write `user_stories/PLAN.md`: a numbered list, one line per Story, in build order. Above 3 Stories, stop and ask the person first.
- Bind external dependencies using pdd-prompting RUNBOOK §21 with deterministic test replies; preserve factory/method handles and name unsupported native effects.
