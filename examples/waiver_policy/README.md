# Waiver Policy Example (Issue #832)

Human-runnable walkthrough for contract waivers, `pdd gate`, and related tooling.

## Prerequisites

From the repository root:

```bash
pip install -e ".[dev]"
```

## Quick verification

Run the bundled script (no API keys required):

```bash
bash examples/waiver_policy/verify.sh
```

Or run the focused pytest gate:

```bash
pytest -vv tests/test_waiver_policy.py tests/test_waiver_integration.py tests/commands/test_gate.py
```

## Manual CLI walkthrough

Fixtures live under `tests/fixtures/contract_check/`.

### 1. Parse and lint waivers

```bash
pdd contracts check tests/fixtures/contract_check/waiver_valid_python.prompt
pdd contracts check tests/fixtures/contract_check/waiver_valid_python.prompt --json
```

Expected: zero errors; JSON includes `"waivers"` with `"status": "active"`.

### 2. Coverage matrix shows waived rules

```bash
pdd checkup coverage tests/fixtures/contract_check/waiver_valid_python.prompt
pdd checkup coverage tests/fixtures/contract_check/waiver_valid_python.prompt --json
```

Expected: rule `R3` is `waived` with waiver id `W1`.

### 3. Gate policy modes

```bash
# Allow waivers (pass)
pdd gate tests/fixtures/contract_check/waiver_valid_python.prompt --allow-waivers

# Forbid any waiver (fail)
pdd gate tests/fixtures/contract_check/waiver_valid_python.prompt --forbid-waivers

# Require expiration dates (fail on missing Expires:)
pdd gate tests/fixtures/contract_check/waiver_missing_fields_python.prompt --require-expiration

# Enforce expiration (fail on expired waiver)
pdd gate tests/fixtures/contract_check/waiver_expired_python.prompt --enforce-expiration
```

### 4. Policy file (optional)

Copy `examples/waiver_policy/gate_policy.yaml` keys into your project `.pddrc`:

```yaml
gate:
  allow_waivers: true
  forbid_waivers: false
  require_expiration: true
  enforce_expiration: true
```

Then run:

```bash
pdd gate tests/fixtures/contract_check/ --policy-file examples/waiver_policy/gate_policy.yaml
```

## Fixture reference

| Fixture | Expected outcome |
|---------|------------------|
| `waiver_valid_python.prompt` | Clean contracts check; gate passes with `--allow-waivers` |
| `waiver_expired_python.prompt` | `EXPIRED_WAIVER` warning; gate fails with `--enforce-expiration` |
| `waiver_missing_fields_python.prompt` | `MISSING_WAIVER_FIELDS` warning; gate fails with `--require-expiration` |
| `waiver_ref_missing_python.prompt` | `WAIVER_REF_MISSING` error |

See `docs/prompting_guide.md` for the canonical `<waivers>` prompt syntax.
