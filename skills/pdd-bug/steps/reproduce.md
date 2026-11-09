# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug. Write down the setup, input, command, expected and actual result.
- If a prompt owns this behavior, follow section 14 of RUNBOOK.md (pdd-prompting skill): write a test from the issue and run `pdd test` on the CURRENT prompt. Report ✗ or ✓, and put its `Prompt tests` line(s) and the report link(s) in your `done` summary as the "before" report.
- If no prompt exists, say so plainly, in the words of section 14.
- If you cannot reproduce it, say why. Never guess a cause.
- After reproducing, record `Cause: <file>#<function> · Flaw: <one sentence> · Class: <short name>` from what you actually found. Record `Relations:` for each other open issue found, with the chosen relation (`needs`, `same cause`, `same class`, `duplicate` or `related`) and a short actual quote from that issue or the code, identifying its source. If none were found, say so. A relation is your decision; a quote alone does not establish it. For a proposed native link, supply its target and direction explicitly; only a necessary-before relation can be a dependency. Do not invent evidence or a cause when reproduction fails.
- In your `done` summary add `Problem:` and one `Case: INPUT | TODAY | EXPECTED` line per issue case (RUNBOOK §15).
- Inventory outside dependencies and bind their ports using pdd-prompting RUNBOOK §21; supply deterministic replies in tests. Preserve factory/method contracts with handles; name any unsupported native effect instead of silently leaving the module unbound.
