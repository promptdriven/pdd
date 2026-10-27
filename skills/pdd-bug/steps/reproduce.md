# reproduce

If pdd has a RUNBOOK.md: write a test from the issue and run `pdd check` on the CURRENT prompt. ✗ means the prompt is wrong, so fix the prompt first. ✓ means the bug is only in the code. Also:
- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug.
- Write down the setup, input, command, expected and actual result.
- If you cannot reproduce it, say why. Never guess a cause.
