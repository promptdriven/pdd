# scope

- Read repo instructions and the files the request touches.
- List every issue request and trusted follow-up in scope.md and `small-change-checklist.json` (RUNBOOK §15); keep pending items visible and quote the issue for any exclusion.
- Run `pdd owner` on planned files. Plan only unowned path d files outside PDD (docs, guides, packages, lockfiles, config, CI or tests); write no Story or prompt.
- If it needs `*.prompt.md`, `user_stories/*.md`, prompt-owned files or product/app code (`src/`, `app/`, etc.), even with no prompt yet, stop and switch to pdd-bug or pdd-feature (in `pdd workflow run`, use `<pdd> workflow ask` to ask the person to run `pdd workflow run bug N` or `feature N`, or proceed only if the person explicitly confirms).
- State the result, planned files, why it stays outside PDD and how to undo it.
- For a CI, config, package or test defect, write `Defect:` and `Not caught because:` in scope.md.
- Name the test command. Put any docs-only/formal exemption in the typed formal block (RUNBOOK §15), not prose.
- Ask only about choices that change the result; never widen scope. Only the person approves gates (RUNBOOK §2).
