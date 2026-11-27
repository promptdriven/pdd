# Traceability review checklist (`trace`)

Check alignment across Stories, paired prompts, product maps or plans, and paired scenarios or tests.

Read paired Stories, scenarios (`tests/*.json`), product docs, and native tests on disk before reporting a gap.

## What to flag

1. **Story contradicting prompt:** A Story acceptance criterion or `## Rules to check` invariant conflicts with the paired prompt rules, defaults, error codes, or `## Domain decisions`.
2. **Dropped requirements:** A Story acceptance criterion, `product/map.md` or `product/plan.md` obligation, or explicit contract promise has no supporting rule in the owning prompt.
3. **Prompt rules with no test:** A material prompt rule, failure branch, or negative invariant has no check in paired scenarios or tests — especially refusal paths that lack an unchanged-state check.
4. **Silent scope drift:** A Story or scenario depends on outputs, flags, or error codes that the owning prompt never defines, or silently weakens a required check.

## Reporting rules

- Quote exact verbatim text from the target file (`file`, `line`, `quote`).
- When reporting a cross-file contradiction between a Story, prompt, scenario, or product doc, also include `cross_file`, `cross_file_line`, and `cross_file_quote` from the other file.
- Focus on real missing coverage or behavior conflicts. Ignore minor phrasing differences that mean the same thing.
