# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Record the smallest safe reproduction: setup, input, command, expected and actual.
- If a prompt owns this behavior, follow section 14 of RUNBOOK.md (pdd-prompting skill), including native cases outside the Runtime interface: write a test from the issue and run `pdd test` on the CURRENT prompt. Report ✗, ✓ or no verdict and its reason. When emitted, put its `Prompt tests` line(s) and the report link(s) in your `done` summary as the "before" report.
- For native cases outside the interface, follow the guide’s native verification route, including the before check and original evidence.
- If no prompt exists, say so plainly, in the words of section 14.
- Record `Defect:` and `Not caught because:` in reproduce.md.
- If you cannot reproduce it, say why. Never guess a cause.
- In your `done` summary add `Problem:` and one `Case: INPUT | TODAY | EXPECTED` line per issue case (RUNBOOK §15).
- Bind outside dependencies using RUNBOOK §21, with deterministic replies and handles. Name unsupported native effects.
