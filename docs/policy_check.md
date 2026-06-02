# Policy Check

`pdd policy check` is a deterministic safety layer that validates generated code against natural-language capability contracts. It uses AST-based static analysis to ensure that modules stay within their allowed side-effect boundaries.

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

## Supported Checks

The initial version of the policy checker focuses on high-risk side effects in Python:

- **Forbidden Imports:** Detects imports of libraries related to networking, shell execution, or sensitive system access.
- **Network Access:** Flags use of libraries like `requests`, `httpx`, `urllib3`, etc., unless explicitly allowed.
- **Shell Execution:** Detects calls to `subprocess`, `os.system`, `shutil.rmtree`, and other shell-like commands.
- **Environment Reads:** Flags access to `os.environ` or `os.getenv` for sensitive environment variables.
- **Sensitive Data Leaks:** Detects logging or printing of variables named `token`, `secret`, `password`, `api_key`, `cvv`, etc.
- **File Writes:** Flags writes to the filesystem outside of the allowed scope.

## Command Usage

```bash
# Check a specific file against its prompt
pdd policy check src/refund_payment.py

# Check a file with an explicit prompt override
pdd policy check src/refund_payment.py --prompt prompts/refund_payment_python.prompt

# Output results as JSON for CI integration
pdd policy check src/refund_payment.py --json

# Run in strict mode (fails on any side-effect if capabilities are missing)
pdd policy check src/refund_payment.py --strict
```

## Handling False Positives (Waivers)

Static analysis can sometimes produce false positives. PDD provides two ways to waive these warnings:

### 1. Inline Waivers

Add a comment on the line that trips the policy checker:

```python
import os
# pdd-policy-ignore: reading non-sensitive env var
config_path = os.getenv("APP_CONFIG_PATH")
```

### 2. Prompt-Level Waivers

Define allowed exceptions in the `<waivers>` section of your prompt:

```xml
<waivers>
- ALLOW os.getenv("APP_CONFIG_PATH"): required for configuration discovery.
</waivers>
```

## Integration with Evidence

Policy checks are automatically included in evidence manifests when run with the `--evidence` flag. This allows you to prove that a module has been validated against its security policy.

```bash
pdd sync --evidence
```

The manifest will contain a `policy` field in the `validation` section:

```json
{
  "validation": {
    "policy": "passed"
  }
}
```
