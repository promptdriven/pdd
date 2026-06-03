# Policy Check

`pdd policy check` is a deterministic safety layer that validates generated code against natural-language capability contracts. It uses AST-based static analysis to ensure that modules stay within their allowed side-effect boundaries.

The same command is also available as `pdd checkup policy check` for checkup workflows. This is **not** the same as `pdd checkup gate`, which evaluates evidence-manifest YAML rules under `.pdd/`.

## Capabilities as structured natural language

`<capabilities>` is structured natural language. You do not need to memorize internal category names or a keyword taxonomy. Write capabilities as clear English statements of what the generated artifact may or must not do.

The checker is deterministic: it maps each bullet conservatively to supported effect categories (network, filesystem, environment, and so on). If a statement is unclear, PDD emits a **warning** with suggested clearer wording. Ambiguous bullets do **not** silently grant risky permissions.

### Quick examples

```xml
<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY write audit files to disk.
- MAY call the Stripe refund API.
- MUST NOT send emails.
- MUST NOT log secrets.
</capabilities>
```

### Clear vs unclear wording

**Good (specific):**

- `MAY write audit files to disk.`
- `MAY call the Stripe refund API.`
- `MAY read required environment variables.`
- `MUST NOT send emails.`
- `MUST NOT log secrets.`

**Unclear:**

- `MAY persist audit records.`

**Why unclear:** “persist” could mean writing to disk, writing to a database, logging, or sending to another service. Prefer a more specific phrase such as `MAY write audit files to disk` or `MAY write audit records to the database`.

Domain verbs such as “MAY write refund records” describe business data operations. They do **not** permit `open(..., "w")`, `Path.write_text`, or other filesystem mutations unless the bullet also names files, disk, or filesystem explicitly.

### When wording is unclear

Example warning:

```text
Capability bullet could not be mapped to a supported effect category: "MAY persist audit records."
Try a clearer phrase such as "MAY write audit files to disk."
```

Example denial when code exceeds recognized allowances:

```text
Generated code writes to the filesystem, but no capability allowing file writes was recognized.
Add a capability such as: "MAY write audit files to disk."
```

Warnings appear in human-readable CLI output and in JSON (`capability_warnings` and unified `findings`).

## Supported checks

The initial version focuses on high-risk side effects in Python:

- **Forbidden imports:** Network, email, and shell-related libraries unless allowed.
- **Network access:** `requests`, `httpx`, `urllib3`, `socket`, etc.
- **Shell execution:** `os.system`, `subprocess.*`, etc.
- **Environment reads:** `os.getenv`, `os.environ`, unless allowed.
- **Sensitive data leaks:** Logging/printing names or string literals suggesting `token`, `secret`, `password`, `cvv`, `pan`, etc. (word-boundary match).
- **File writes:** `open(..., "w")`, `Path(...).write_text` / `write_bytes`, `Path(...).open(..., "w")`, `os.remove`, etc. Read-only `open()` is not flagged.

### Implementation coverage (reference, not required syntax)

The checker uses conservative substring mapping. These word families help the implementation recognize intent; they are **not** a language you must memorize:

| Effect family | Example words in a bullet |
|---------------|---------------------------|
| Network / HTTP | `network`, `api`, `http`, `endpoint`, `provider`, `request`, `url` |
| Shell | `shell`, `command`, `subprocess`, `exec` |
| Filesystem | `file`, `files`, `filesystem`, `disk`, `storage`, `write file`, `on disk` |
| Environment | `env`, `environment`, `configuration` |
| Email | `email`, `mail`, `smtp` |

`MUST NOT` bullets that mention a family block that category; `MAY` / `SHOULD` bullets that map clearly to a family allow it.

### Deferred in v1

- Full static taint analysis
- Import/call allowlists against arbitrary “out-of-scope” modules (use `<pdd-dependency>` + review instead)
- Parsing structured `ALLOW …` waiver lines (prompt-level waivers only match when category and message both appear in the waiver text)

## Command usage

```bash
# Top-level command (issue #828)
pdd policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt

# Checkup namespace alias
pdd checkup policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt

# JSON for CI (capabilities, issues, capability_warnings, findings)
pdd policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt --json

# Strict: flag side effects even when <capabilities> is missing
pdd policy check src/refund_payment.py --strict

# Evidence manifest with validation.policy
pdd policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt --evidence
```

Directory targets skip common vendor folders (`.git`, `venv`, `node_modules`, `__pycache__`, `.pdd`, etc.).

### Exit codes

| Code | Meaning |
|------|---------|
| 0 | All targets passed |
| 1 | Policy violations (default mode) |
| 2 | Violations in `--strict` mode, or system/parse errors |

Capability **authoring warnings** do not change the exit code by themselves; enforcement **errors** do.

## Waivers

Add `# pdd-policy-ignore` on the line above (or the same line as) a flagged statement to suppress a specific finding when review accepts the risk.

Prompt-level `<pdd-policy-waiver>` blocks can match findings when both category and message text appear in the waiver (see prompt contract docs).
