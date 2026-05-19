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

