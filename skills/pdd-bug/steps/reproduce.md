# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug. Write down the setup, input, command, expected and actual result.
- If a prompt owns this behavior, follow section 14 of RUNBOOK.md (pdd-prompting skill): write a test from the issue and run `pdd check` on the CURRENT prompt. Report ✗ or ✓, and put its `Runtime check` line(s) and the report link(s) in your `done` summary as the "before" report.
- If no prompt exists, say so plainly, in the words of section 14.
- If you cannot reproduce it, say why. Never guess a cause.
- Inventory outside dependencies and bind their ports using pdd-prompting RUNBOOK §21; supply deterministic replies in tests. Preserve factory/method contracts with handles; name any unsupported native effect instead of silently leaving the module unbound.
