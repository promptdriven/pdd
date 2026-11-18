# understand

- Read the issue, repo rules and code.
- With a product plan, read `product/map.md`, `product/plan.md` and contracts first; prefix Stories with map IDs (`P01-menu.md`) and propose a plan PR, never edit `contracts/`.
- State the goal, unchanged behavior and out-of-scope items; separate decisions, code and open questions.
- If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise.
- Scope triage: use `0` Stories + one `"No Story:"` PR line when no user-visible outcome changes, edit the existing Story when modifying an existing slice, or plan `1` Story per cohesive standalone user loop over injected `<port>.<op>` ports (never split on `"and"`).
- With 1 standalone user loop, write one Story and no plan. With multiple independent loops, write `user_stories/PLAN.md`: a numbered list, one line per Story, in build order, and confirm broad multi-Story splits first.
- Bind outside ports per RUNBOOK §21 with deterministic replies; keep factory/method handles and name unsupported native effects.
