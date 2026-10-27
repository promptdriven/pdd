# verify

- Run the replay test, the new cases, the regression tests and the repo's required checks.
- Run the replay test on a throwaway copy with ONE planted mistake. At least one case must fail there. A crash or an import error does not count.
- Show that `git diff <PR 1 head> -- tests/<story>.json` is empty.
- In verify.md, write `## Test vectors` with one row per case: | Case | Criterion | Input | Expected | Prompt (PR 1) | Code (PR 2) | Result |
- A target that the replay cannot check is Not replayed, with the reason. It is never a pass.
- If a case fails, write "✗ N vectors fail" as the first line of verify.md.
- Report the exact commands, exit codes and real output. Name what no test covers.
