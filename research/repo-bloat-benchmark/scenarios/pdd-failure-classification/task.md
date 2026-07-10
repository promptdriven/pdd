# Bug report: timed-out runs misclassified when the log also mentions an import error

`classify_failure` triages combined pytest/verification output so the fix
loop can decide whether another LLM fix attempt is worth the budget.

When a test run **times out**, the captured log very often *also* contains an
import/collection marker — a module that hangs during import produces both
`ERROR collecting …` (or `ModuleNotFoundError`, `ImportError`, …) and a
timeout marker (`timed out after …`, `Failed: Timeout (>…)`, `deadline
exceeded`, …). For such mixed logs `classify_failure` currently returns
`FailureKind.SYNTAX_IMPORT`, so the fix loop burns retries on "syntax fixes"
for runs that actually died of a timeout.

Expected behavior: a log that matches a timeout marker is
`FailureKind.TIMEOUT_FLAKY`, regardless of whether syntax/import markers are
also present. Pure syntax/import logs (no timeout marker) must keep
classifying as `FailureKind.SYNTAX_IMPORT`, and the assertion/logic default
must not change.

## Constraints

- Fix the defect in the library code under `src/pdd/`.
- Do not modify anything under `tests/`.
- The visible suite (`pytest tests/visible -q`) must keep passing.
