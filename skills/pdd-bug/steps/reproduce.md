# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug. Write down the setup, input, command, expected and actual result.
- If a prompt owns this behavior, follow section 11 of RUNBOOK.md (pdd-prompting skill): write a test from the issue and run `pdd check` on the CURRENT prompt. Report ✗ or ✓.
- If no prompt exists, say plainly: "No prompt exists yet for this behavior, so the bug can only be in the code."
- If you cannot reproduce it, say why. Never guess a cause.
