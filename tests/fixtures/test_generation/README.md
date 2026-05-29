# Contract-rule test generation fixtures

Used by issue #821 / PR #1283 regression and CLI smoke tests.

- `refund_policy_python.prompt` — module prompt with one `MUST` and one `MUST NOT` rule (`R1`, `R2`).
- `refund_policy.py` — minimal implementation under test.

Run smoke:

```bash
PYTHONPATH=. pytest -q tests/commands/test_contract_rule_test_smoke.py
```

Manual `pdd test` (requires API keys):

```bash
pdd --local test --manual refund_policy_python.prompt refund_policy.py \
  --existing-tests /path/to/test_refund_policy.py --merge
```
