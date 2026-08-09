<!-- pdd-story-contract derived-from-story="../story__pdd_contracts_check_gate.md" story-hash="8e7cc7402eb25238" issue-ref="https://github.com/promptdriven/pdd/issues/1698" -->

# Contract: Contract checks catch malformed prompt rules

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_contracts_check_gate.md`), not this contract.

## Covers

- R1: `pdd contracts check TARGET` accepts prompt files and directories with an optional stories directory.
- R2: The deterministic checker reports malformed or duplicate rule IDs.
- R3: The checker reports unknown story coverage references and missing coverage for required rules.
- R4: Cross-module `## Covers` references are parsed without confusing prompt names and rule IDs.
- R5: Clean prompts exit successfully without requiring LLM calls.

## Context

The deterministic contract-rule checker is the closest story-regression analogue
to Python unit tests for prompt obligations: it parses local files, checks known
failure modes, and exits without provider access.

## Acceptance Criteria

1. Given a prompt with sequential contract rules and valid story coverage, when `pdd contracts check` runs, then it exits successfully.
2. Given duplicate, malformed, or non-sequential rule IDs, when the checker runs, then it reports the exact contract-rule issue.
3. Given a story covers an unknown rule ID, when the checker runs with the stories directory, then it reports the unknown reference.
4. Given a cross-module cover reference such as `prompts/foo.prompt#R3`, when parsing covers entries, then the checker attributes the reference to the right prompt and rule.
5. Given a target directory, when the checker runs, then it aggregates deterministic results without invoking an LLM.

## Oracle

These details matter for pass/fail:
- file and directory targets are accepted
- malformed or duplicate rule IDs are reported
- unknown story references are reported
- cross-module coverage references retain prompt and rule identity
- clean inputs exit successfully without provider calls

## Non-Oracle

These details should not matter:
- exact table styling
- exact order of unrelated clean files in directory output
- wording of non-actionable helper text
- downstream generation behavior

## Negative Cases

- A duplicate rule ID must not be silently treated as two valid obligations.
- A story reference to an unknown rule must not count as coverage.
- A malformed cross-module reference must not be attributed to the wrong prompt.
- The checker must not require a model key for deterministic validation.

## Non-Goals

- This story does not verify generated implementation code.
- This story does not prescribe all future contract-rule lint checks.
- This story does not cover hosted dashboards.

## Candidate Prompts

- `prompts/commands/contracts_python.prompt` - owns the `pdd contracts check` CLI.
- `prompts/contract_check_python.prompt` - owns deterministic contract validation.
- `prompts/contract_ir_python.prompt` - owns rule and cover reference parsing.

## Notes

This story protects the contract gate as a local, fast, unit-test-like check for
prompt rules.
