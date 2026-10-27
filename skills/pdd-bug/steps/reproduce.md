# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug. Write down the setup, input, command, expected and actual result.
- If a prompt owns this behavior, follow section 11 of RUNBOOK.md (pdd-prompting skill): write a test from the issue and run `pdd check` on the CURRENT prompt. ✗ means the prompt is wrong, so fix the prompt first. ✓ means the bug is only in the code.
- If no prompt exists, say plainly: "No prompt exists yet for this behavior, so the bug can only be in the code."
- Do not add a failing repo test here: it goes to PR 2.
- If you cannot reproduce it, say why. Never guess a cause.
