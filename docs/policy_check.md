# Policy Check

`pdd checkup policy check` is a deterministic safety layer that validates generated code against natural-language capability contracts. It uses AST-based static analysis to ensure that modules stay within their allowed side-effect boundaries.

This is **not** the same as `pdd checkup gate`, which evaluates evidence-manifest YAML rules under `.pdd/`. Capability policy checks are driven by `<capabilities>` in module prompts.

## Capabilities and Side Effects

In PDD, you can define what a module is allowed (or forbidden) to do using the `<capabilities>` section in your prompt:

```xml
<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY call the payment provider refund endpoint.
- MUST NOT send emails.
- MUST NOT modify customer profile records.
- MUST NOT read unrelated environment variables.
- MUST NOT log provider secrets, bearer tokens, or card PAN.
</capabilities>
```

The policy checker parses these rules and enforces them against the generated Python code.

### Keyword vocabulary (v1)

Capabilities are matched with simple substring checks on each bullet (case-insensitive). Use words from these families so the checker understands intent:

| Category | Example words in the bullet |
|----------|-----------------------------|
| Network / HTTP | `network`, `api`, `http`, `endpoint`, `provider`, `request`, `url` |
| Shell | `shell`, `command`, `subprocess`, `exec` |
| Files | `file`, `write`, `delete`, `persist`, `storage` |
| Environment | `env`, `environment`, `configuration` |
| Email | `email`, `mail`, `smtp` |

`MUST NOT` bullets that mention a family block that category; `MAY` / `SHOULD` bullets that mention a family allow it.

## Supported Checks

The initial version focuses on high-risk side effects in Python:

- **Forbidden imports:** Network, email, and shell-related libraries unless allowed.
- **Network access:** `requests`, `httpx`, `urllib3`, `socket`, etc.
- **Shell execution:** `os.system`, `subprocess.*`, etc.
- **Environment reads:** `os.getenv`, `os.environ`, unless allowed.
- **Sensitive data leaks:** Logging/printing names or string literals suggesting `token`, `secret`, `password`, `cvv`, `pan`, etc. (word-boundary match).
- **File writes:** `open(..., "w")`, `Path(...).write_text` / `write_bytes`, `Path(...).open(..., "w")`, `os.remove`, etc. Domain bullets such as “MAY write refund records” do **not** authorize filesystem writes. Read-only `open()` is not flagged.

### Deferred in v1

- Full static taint analysis
- Import/call allowlists against arbitrary “out-of-scope” modules (use `<pdd-dependency>` + review instead)
- Parsing structured `ALLOW …` waiver lines (prompt-level waivers only match when category and message both appear in the waiver text)

## Command Usage

```bash
# Check a specific file (prompt auto-discovered when possible)
pdd checkup policy check src/refund_payment.py

# Explicit prompt
pdd checkup policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt

# JSON for CI (capabilities + issues)
pdd checkup policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt --json

# Strict: flag side effects even when <capabilities> is missing
pdd checkup policy check src/refund_payment.py --strict

# Evidence manifest with validation.policy
pdd checkup policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt --evidence
```

Directory targets skip common vendor folders (`.git`, `venv`, `node_modules`, `__pycache__`, `.pdd`, etc.).

### Exit codes

| Code | Meaning |
|------|---------|
| `0` | All targets passed |
| `1` | Violations found (default mode) |
| `2` | Violations in `--strict` mode, or a file could not be parsed |

## Handling False Positives (Waivers)

### Inline waivers

```python
import os
# pdd-policy-ignore: non-secret config path
config_path = os.getenv("APP_CONFIG_PATH")
```

### Prompt-level waivers (experimental)

`<waivers>` entries suppress a finding only when **both** the issue category and message substring appear in the waiver block. Prefer inline waivers until structured waiver IDs land.

## Integration

- **`pdd checkup --pr --review-loop`:** When a changed `.py` file has a prompt with `<capabilities>`, a `policy:<path>` gate runs `pdd checkup policy check`.
- **`pdd checkup drift`:** Runs policy check when the prompt defines `<capabilities>` (not when only evidence gate YAML exists).
- **Evidence:** `--evidence` sets `validation.policy` to `passed` or `failed`. Sync may populate the same field via `validation_from_sync`.
