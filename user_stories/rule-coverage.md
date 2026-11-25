# Trace changed domain rules to tests

As a developer reviewing a pull request with `pdd lint --diff` and `pdd prove`, I want changed rule IDs in `## Domain decisions` and `## Rules to check` traced mechanically to formal, scenario, and native tests or explicit `Not proved:` disclosures, so that modified rules never ship silently untested.

## Acceptance criteria

1. When a changed prompt adds `LED-H1` (referenced in `test/ledger.formal.test.mjs`), `LED-H2` (referenced in `test/runtime/ledger.json` step `LED-H2-clamp`), `LED-H3` (marked `Not proved: preview formatting only`), and `LED-H4` (unreferenced), `pdd prove --json` reports `LED-H1` as `covered` (`tiers: ["formal"]`), `LED-H2` as `covered` (`tiers: ["scenario"]`), `LED-H3` as `not_proved` with reason `"preview formatting only"`, and `LED-H4` as `uncovered`, and `pdd lint --diff` emits a non-blocking warning only for `LED-H4` while exiting with code 0.
2. When a changed Story under `## Rules to check` modifies bullet `TR-C1` and a native test file references `TR-C1`, `TR-C1` is reported as `covered` with `tiers: ["native"]` and zero warnings, while an unchanged rule `TR-H1` from the merge base is omitted from the report.
3. When a changed prompt edits plain-prose `## Domain decisions` bullets without explicit rule IDs or mentions rule-like text only inside fenced code blocks, zero rules are extracted and zero warnings are emitted.
4. When `LED-H4` is referenced only in `src/ledger.mjs` or only as a substring inside `LED-H40` or `XLED-H4` in tests, `LED-H4` stays `uncovered` and triggers the non-blocking warning.
5. When a rule carries an empty `Not proved:` marker with no reason text, it stays `uncovered` rather than `not_proved`.

## Rules to check

- **RC-1:** Uncovered changed rules emit non-blocking warnings only and never make `pdd lint --diff` exit nonzero or flip `pdd prove` to `Failed` or `Not proved`. Forbidden: failing exit code solely due to an uncovered rule.
- **RC-2:** Plain-prose bullets, fenced code blocks, and unchanged base rules never produce warnings. Forbidden: reporting unchanged merge-base rules or plain prose as uncovered rules.
- **RC-3:** Only real formal, scenario, and native test files with whole-word rule ID matches count as coverage. Forbidden: counting production source files or substring matches such as `LED-H40` as coverage for `LED-H4`.
