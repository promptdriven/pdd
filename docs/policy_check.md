# PDD Policy Check

Target-neutral capability policy checking for PDD prompts. Verifies that a
generated artifact's runtime behavior matches the `<capabilities>` block
declared in its source prompt.

## Canonical command

```bash
pdd checkup policy check PROMPT ARTIFACT [--target TARGET] [--json]
```

## Quick start

```bash
# Check a Python module against its prompt's <capabilities> block
pdd checkup policy check prompts/refund_payment_python.prompt src/refund_payment.py

# Explicit target (same as default)
pdd checkup policy check prompts/refund_payment_python.prompt src/refund_payment.py --target python

# Machine-readable JSON output
pdd checkup policy check prompts/refund_payment_python.prompt src/refund_payment.py --json

# Check an unsupported target (returns structured unsupported response)
pdd checkup policy check prompts/checkout_typescript.prompt src/checkout.ts --target typescript --json
```

## `--target` flag

| Value | Backend | Notes |
|-------|---------|-------|
| `python` (default) | `policy_backends.python_ast` | Static AST analysis of Python source files |
| *(other)* | — | Returns `{"status": "unsupported", ...}` without crashing |

Omitting `--target` defaults to `python` for backward compatibility.

## JSON output schema

### Supported target — findings present

```json
{
  "target": "python",
  "contract": {
    "capabilities_present": true,
    "effect_count": 8
  },
  "findings": [
    {
      "severity": "error",
      "effect": {"action": "send", "resource": "email"},
      "rule": "must_not_send_email",
      "message": "Found forbidden email-sending call at line 42",
      "location": {
        "file": "src/refund_payment.py",
        "line": 42,
        "symbol": "sendgrid.SendGridAPIClient"
      }
    }
  ]
}
```

### Supported target — clean run

```json
{
  "target": "python",
  "contract": {"capabilities_present": true, "effect_count": 3},
  "findings": []
}
```

### Unsupported target

```json
{
  "target": "typescript",
  "status": "unsupported",
  "message": "No policy backend registered for target: typescript"
}
```

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | No findings (clean) or unsupported target (structured response, no crash) |
| `1` | One or more policy findings with `severity: error` |

## Fields

### `contract`

| Field | Type | Description |
|-------|------|-------------|
| `capabilities_present` | bool | Whether a `<capabilities>` block was found in the prompt |
| `effect_count` | int | Number of effect lines parsed from the `<capabilities>` block |

### `findings[]`

| Field | Type | Description |
|-------|------|-------------|
| `severity` | string | `"error"` or `"warning"` |
| `effect` | object | `{"action": str, "resource": str}` from the violated capability rule |
| `rule` | string | Machine-readable rule identifier (e.g. `"must_not_send_email"`) |
| `message` | string | Human-readable description of the finding |
| `location` | object | `{"file": str, "line": int, "symbol": str}` — `line` and `symbol` are omitted when unavailable |

## Evidence manifest integration

Pass `--evidence` to record policy check results in the run manifest under the
`policy_check` key. See [docs/evidence_manifest.md](evidence_manifest.md) for
the full schema.

```bash
pdd checkup policy check prompts/refund_payment_python.prompt src/refund_payment.py --json --evidence
```

## Related commands

- **Contract lint:** `pdd checkup contract check` — validates `<contract_rules>` syntax and coverage.
- **Coverage matrix:** `pdd checkup coverage` — rule-to-story/test coverage report.
- **Evidence gate:** `pdd checkup gate` — evidence-manifest policy enforcement before merge.
