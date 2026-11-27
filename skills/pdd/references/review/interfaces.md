# Interfaces review checklist (`interfaces`)

Check cross-file contracts between target files and their linked neighbors, shared contracts, and `kind: native-only` adapters.

Read the linked files on disk before reporting any mismatch. Never guess what an unread neighbor says.

## What to flag

1. **Route, field, port, or error-code mismatch:** Caller and callee, prompt and shared contract, or `kind: native-only` adapter and checkable prompt disagree on operation name, `<port>.<op>` signature, HTTP route, field name, type, unit, or error code.
2. **Sibling rule contradictions:** Two linked files disagree on boundary comparisons (`<` vs `<=`), default values, fail-open vs. fail-closed behavior, retry/timeout bounds, or state transitions.
3. **Duplicate policy owners:** Two sibling prompts each define independent copies of the same rule table, classification, or invariant instead of calling one canonical owning prompt.
4. **Adapter-to-prompt drift:** A `kind: native-only` prompt omits a required port error path, reverses argument order, adds an undocumented side effect, or contradicts the checkable prompt it binds.

## Reporting rules

- **Both-file quote rule:** Every `interfaces` finding MUST cite exact verbatim quotes from BOTH files: `file`, `line`, `quote` AND `cross_file`, `cross_file_line`, `cross_file_quote`.
- Any finding missing either quote, pointing both quotes to the same file, or failing disk quote verification is dropped automatically.
- Flag only real contract or behavior conflicts. Skip harmless prose differences.
