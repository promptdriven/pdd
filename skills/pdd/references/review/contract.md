# Contract review checklist (`contract`)

Check every target prompt and Story for internal soundness and clear, testable rules.

## What to flag

1. **Internal contradictions:** Prose, tables, diagrams, or examples inside the same file disagree on defaults, limits, status codes, ordering, or precedence.
2. **Prose vs. table or schema mismatch:** A table, JSON schema, or example uses a different field name, type, unit, required flag, or value range than the surrounding rules.
3. **Rollback vs. durable side effects:** An operation rolls back a transaction while also claiming an audit entry, counter, or event survives (or vice versa) without stating a separate durability boundary.
4. **Missing boundary, null, or error outcomes:** An external port call, authorization check, write failure, or boundary input (`null`, missing, empty, `0`, negative, oversized) has no stated refusal code, output shape, or surviving state.
5. **Underspecified I/O:** An operation accepts or returns bare untyped `"object"`, omits units, timezones, or rounding rules, or leaves error codes unnamed.
6. **Leaked code or private internals:** A prompt pastes imperative implementation code or mandates private helper names or internal-only flags. A Story leaks internal file paths, SQL tables, private struct fields, or vague criteria ("works cleanly", "handles errors properly").

## Reporting rules

- Report only concrete, high-impact defects that can cause wrong behavior or broken builds.
- Quote exact verbatim text from the target file and give its 1-based line number.
- Ignore style preferences, naming taste, and harmless wording variations.
- Return an empty `findings` array when the file is sound.
