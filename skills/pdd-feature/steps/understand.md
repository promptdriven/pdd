# understand

- Read the issue, the repo instructions and the related code.
- For a product plan, read `product/map.md`, `product/plan.md` and named contracts first. Prefix Story files with map IDs (e.g. `P01-menu.md`). Never edit `contracts/`; propose a plan PR.
- State the wanted result, what must not change and what is out of scope.
- Keep apart what is decided, what the code does now and open questions.
- If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise.
- Count the separate behaviors. With 1 behavior, write one Story and no plan. With more, write `user_stories/PLAN.md`: a numbered list, one line per Story, in build order.
- Inventory outside dependencies and bind ports (pdd-prompting RUNBOOK §21) with deterministic test replies. Keep factory/method handles; name any unsupported native effect.
- Case outside a prompt's declared interface: widen the prompt and interface first (draft); ask a route question only when prose cannot express the behavior.
