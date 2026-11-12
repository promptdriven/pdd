# reproduce

- Read issue, repo instructions and owning prompt.
- Record smallest safe case: setup, input, command, expected, actual.
- If a prompt owns this behavior, follow RUNBOOK.md section 14: write a test from the issue and run `pdd test` on the CURRENT prompt. Report ✗ or ✓; put its `Prompt tests` line(s) and the report link(s) in your `done` summary as the "before" report.
- If no prompt exists, say so plainly, in the words of section 14.
- Record `Defect:` and `Not caught because:` in reproduce.md.
- If reproduced, inspect code; record `Cause: <file>#<function> · Flaw: <one sentence> · Class: <short name>`. Find open issues sharing cause/class; record `Relations: <JSON array>` (`[]` if none). Read `../bug-cause.md`; choose relations and links explicitly.
- If unreproduced, say why; never guess a cause.
- In `done` add `Problem:` and `Case: INPUT | TODAY | EXPECTED` per case (§15).
- Inventory outside dependencies; bind ports with deterministic replies (§21). Preserve factory/method handles; name unsupported effects.
