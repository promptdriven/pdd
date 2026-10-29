# understand

- Read the issue, the repo instructions and the related code.
- State the wanted result, what must not change and what is out of scope.
- Keep apart what is decided, what the code does now and open questions.
- If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise.
- Count the separate behaviors. With 1 behavior, write one Story and no plan. With more, write `user_stories/PLAN.md`: a numbered list, one line per Story, in build order.
- Inventory outside dependencies and bind their ports using pdd-prompting RUNBOOK §21; supply deterministic replies in tests. Preserve factory/method contracts with handles; name any unsupported native effect instead of silently leaving the module unbound.
