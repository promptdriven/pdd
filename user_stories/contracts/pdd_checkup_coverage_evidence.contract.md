<!-- pdd-story-contract derived-from-story="../story__pdd_checkup_coverage_evidence.md" story-hash="df12c306985649b5" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Coverage reports show rule evidence

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_checkup_coverage_evidence.md`), not this contract.

## Covers

- R1: `pdd checkup coverage TARGET` delegates to deterministic coverage analysis.
- R2: The rule-to-evidence matrix reports story, test, waiver, and missing evidence per rule.
- R3: JSON output remains machine-readable for CI and agent review.
- R4: Legacy prompts without contract rules are handled without false failures.
- R5: Cross-unit stories are attributed without being double-counted in global metrics.

## Context

Coverage reporting turns contract rules into a deterministic coverage matrix.
For a regression suite that behaves like Python unit tests, reviewers need this
local command to expose evidence gaps without relying on a live model.

## Acceptance Criteria

1. Given a prompt with contract rules and linked stories, when coverage runs, then each rule row lists the matching story evidence.
2. Given a test explicitly names a rule ID, when coverage runs with a tests directory, then that test appears as evidence for the rule.
3. Given a waiver covers a rule, when coverage runs, then the waiver status and expiry are visible.
4. Given a rule has no story, test, or waiver, when coverage runs, then the gap is reported instead of passing silently.
5. Given `--json` is requested, when coverage runs, then output is structured enough for CI to consume.
6. Given a prompt has no contract rules, when coverage runs, then it is treated as legacy-safe rather than a hard error.

## Oracle

These details matter for pass/fail:
- command delegation to deterministic coverage analysis
- rule-to-evidence matrix contents
- missing evidence remains visible
- JSON output can be consumed by CI
- legacy prompts without contract rules do not fail spuriously
- cross-unit stories are not double-counted

## Non-Oracle

These details should not matter:
- exact Rich table styling
- exact ordering of unrelated rule rows
- model/provider configuration
- implementation helper names

## Negative Cases

- A missing story/test/waiver must not be hidden by an aggregate percentage.
- A test that does not name a rule ID must not count as rule evidence.
- Expired or malformed waivers must not count as clean coverage.
- Cross-unit stories must not inflate global coverage counts.

## Non-Goals

- This story does not prescribe a hosted dashboard.
- This story does not require live provider credentials.
- This story does not verify the semantic correctness of every story body.

## Candidate Prompts

- `prompts/commands/checkup_python.prompt` - owns `pdd checkup coverage` delegation.
- `prompts/coverage_contracts_python.prompt` - owns the deterministic rule-to-evidence matrix.
- `prompts/contract_ir_python.prompt` - owns contract rule parsing.

## Notes

This story protects deterministic coverage reporting as the suite's equivalent
of a local unit-test coverage gate.
