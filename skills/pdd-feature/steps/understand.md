# understand

- Read the issue, repo rules and code.
- With a product plan, read `product/map.md`, `product/plan.md` and contracts first; prefix Stories with map IDs (`P01-menu.md`) and propose a plan PR, never edit `contracts/`.
- State the goal, unchanged behavior and out-of-scope items; separate decisions, code and open questions.
- If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise.
- Scope triage: `0` Runtime Stories (`kind: native-only` + `node --test`) applies only if no user-visible outcome changes or an existing Story checks the enclosing user flow; if native/crypto/I/O affects an uncovered user flow, plan the enclosing checkable flow prompt + `1` Story over an injected port (plus any thin `kind: native-only` adapter).
- Count the separate behaviors. With 1 behavior, write one Story and no plan. With 2 or 3, write `user_stories/PLAN.md`: a numbered list, one line per Story, in build order. Above 3, stop and ask first.
- Bind outside ports per RUNBOOK §21 with deterministic replies; keep factory/method handles and name unsupported native effects.
