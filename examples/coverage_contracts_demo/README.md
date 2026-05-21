# Contract Coverage Demo

This demo shows `pdd coverage --contracts` on a small refund prompt with rule IDs, story coverage, executable-test references, an unchecked rule, a waiver, and a deterministic failed story.

Run from the repository root:

```bash
pdd coverage --contracts \
  --stories-dir examples/coverage_contracts_demo/user_stories \
  --tests-dir examples/coverage_contracts_demo/tests \
  examples/coverage_contracts_demo/prompts/refund_payment_python.prompt
```

JSON form:

```bash
pdd coverage --contracts --json \
  --stories-dir examples/coverage_contracts_demo/user_stories \
  --tests-dir examples/coverage_contracts_demo/tests \
  examples/coverage_contracts_demo/prompts/refund_payment_python.prompt
```

Expected statuses:

- `R1`: checked
- `R2`: story-only
- `R3`: test-only
- `R4`: story-only
- `R5`: unchecked
- `R6`: waived
- `R7`: failed

To verify that the same prompt is also structured enough for deterministic
contract IR, run:

```bash
pdd contracts compile --json \
  examples/coverage_contracts_demo/prompts/refund_payment_python.prompt
```

Coverage and compilation answer different questions:

- `pdd coverage --contracts` shows whether rules have story/test/waiver evidence.
- `pdd contracts compile` shows whether rules can become machine-readable IR.

## Legacy-safe behavior

`prompts/legacy_utility_python.prompt` is intentionally a **non-contract prompt**
(no `<contract_rules>` section). It exists to confirm that the contracts
commands degrade gracefully on legacy prompts:

```bash
pdd coverage --contracts --json \
  examples/coverage_contracts_demo/prompts/legacy_utility_python.prompt
```

Expected output: `has_contract_rules: false`, zero rule rows, exit 0. Use this
to verify upgrades to coverage tooling don't regress mixed repositories.
