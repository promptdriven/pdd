# reproduce

- Read the issue, repo instructions and the prompt that owns the behavior.
- Find the smallest safe input that shows the bug. Write down the setup, input, command, expected and actual result.
- If a prompt owns this behavior, follow section 14 of RUNBOOK.md (pdd-prompting skill): write a test from the issue and run `pdd test` on the CURRENT prompt. Report ✗ or ✓, and put its `Prompt tests` line(s) and the report link(s) in your `done` summary as the "before" report.
- If no prompt exists, say so plainly, in the words of section 14.
- Record `Defect:` and `Not caught because:` in reproduce.md.
- When reproduced, inspect the code and record `Cause: <file>#<function> · Flaw: <one sentence> · Class: <short name>`. Find other open issues sharing a cause or class and record `Relations: <JSON array>` (use `[]` when none found). Each entry has `issue`, `kind` (needs / same cause / same class / duplicate / related), `source` (`issue:N` for that issue or `code:PATH`), `quote` (short exact text), and `link`. Choose the relation and link explicitly: needs → blocked by; duplicate → duplicate; same cause → none or blocked by; same class → none or sub-issue under an existing issue titled `Class: <short name>`; related → none. pdd checks every quote before writing links; quote presence does not prove the diagnosis. Use the repository's bug-cause contract for the transport and validation rules. Never infer a dependency from shared cause alone.
- If you cannot reproduce it, say why. Never guess a cause.
- In your `done` summary add `Problem:` and one `Case: INPUT | TODAY | EXPECTED` line per issue case (RUNBOOK §15).
- Inventory outside dependencies and bind their ports using pdd-prompting RUNBOOK §21; supply deterministic replies in tests. Preserve factory/method contracts with handles; name any unsupported native effect instead of silently leaving the module unbound.
