# Contract Compile

`pdd contracts compile` converts parseable `<contract_rules>` into a stable JSON
intermediate representation. This is the first deterministic step toward formal
verification: raw prompt prose is not verified directly; controlled
natural-language rules compile into machine-readable obligations.

## Quick Start

```bash
pdd contracts compile prompts/refund_payment_python.prompt
pdd contracts compile --json prompts/refund_payment_python.prompt
pdd contracts compile prompts/
```

Prompts without `<contract_rules>` are legacy-safe and exit `0` with no contract
IR.

Use this command after authoring checks:

```bash
pdd prompt lint --strict prompts/refund_payment_python.prompt
pdd contracts check prompts/refund_payment_python.prompt
pdd coverage --contracts prompts/refund_payment_python.prompt
pdd contracts compile --authoring --json prompts/refund_payment_python.prompt
pdd contracts compile --json prompts/refund_payment_python.prompt
pdd contracts review --llm prompts/refund_payment_python.prompt
```

Use `pdd prompt lint --ambiguity prompts/refund_payment_python.prompt`
during authoring when you want LLM guidance on how to rewrite vague rules into
this compile-friendly shape. The LLM coaching step is advisory; `contracts compile`
is deterministic.

## Contract Shape

The v1 compiler is intentionally conservative. Each compiled rule should have:

- an explicit stable rule ID such as `R1` or `R-001`
- a `When ...` condition
- at least one observable obligation

This format is preferred:

```text
R<N> - Short rule name
When <specific condition>,
the service MUST <observable outcome> and MUST NOT <forbidden outcome>.
```

Example:

```text
<contract_rules>
R1 - Reject duplicate refund
When a request has the same tenant ID and idempotency key as an accepted refund,
the service MUST return HTTP 409 and MUST NOT write a new refund record.
</contract_rules>
```

Compiles to:

```json
[
  {
    "version": "pdd.contract_ir.v1",
    "path": "prompts/refund_payment_python.prompt",
    "has_contract_rules": true,
    "rule_count": 1,
    "error_count": 0,
    "rules": [
      {
        "id": "R1",
        "title": "Reject duplicate refund",
        "modal": "MUST",
        "condition": "a request has the same tenant ID and idempotency key as an accepted refund",
        "obligations": [
          {
            "modal": "MUST",
            "type": "return",
            "value": {"http_status": 409},
            "text": "MUST return HTTP 409"
          },
          {
            "modal": "MUST NOT",
            "type": "write",
            "value": {"target": "a new refund record"},
            "text": "MUST NOT write a new refund record"
          }
        ],
        "raw": "R1 - Reject duplicate refund\nWhen ..."
      }
    ],
    "compile_errors": []
  }
]
```

## Recognized Obligations

The v1 compiler recognizes these observable forms:

| Form | IR type |
|------|---------|
| `MUST return HTTP 409` | `return` with `http_status` |
| `MUST return a JSON object` | `return` with `target` |
| `MUST write one upload record` | `write` with `target` |
| `MUST NOT write a new record` | `write` with modal `MUST NOT` |
| `MUST NOT call provider_client` | `call` with modal `MUST NOT` |
| `MUST emit refund.accepted` | `emit` |
| `MUST raise ValueError` | `raise` |

`SHOULD`, `MAY`, and `SHALL` forms are preserved in the `modal` field, but
verification adapters should decide which modals are hard obligations.

## Compile Errors

| Code | Meaning |
|------|---------|
| `UNSTABLE_RULE_ID` | Rule lacks an explicit ID such as `R1` |
| `MISSING_CONDITION` | Rule does not contain a parseable `When ...` condition |
| `NO_OBSERVABLE_OBLIGATION` | Rule has no recognized observable obligation |

The compiler still includes partially compiled rules in JSON output when
possible. A rule can therefore appear in `rules` and also have a
`compile_errors` entry. Consumers should treat `error_count > 0` as a failed
compile.

Exit codes:

| Code | Meaning |
|------|---------|
| `0` | All contract rules compiled, or no `<contract_rules>` exist |
| `2` | One or more contract rules could not compile cleanly |

## Role In The Verification Pipeline

Use the tools in this order:

```bash
pdd prompt lint --strict prompts/
pdd contracts check prompts/
pdd coverage --contracts prompts/
pdd contracts compile --json prompts/
```

`prompt lint` improves authoring clarity. `contracts check` validates contract
structure. `coverage --contracts` maps rules to stories, tests, and waivers.
`contracts compile` produces the deterministic IR that future verification
adapters can consume.

The current command stops at IR generation. It does not prove implementation
correctness by itself. A future `pdd contracts verify` command can consume this
IR to generate property tests, runtime assertions, OpenAPI checks, state-machine
checks, or formal models.

## Fixtures And Tests

Runnable fixtures live under `tests/fixtures/contract_compile/`.

Useful test commands:

```bash
pytest tests/test_contract_compile.py tests/commands/test_contracts_compile.py -q
pytest tests/test_prompt_guidance.py tests/commands/test_prompt_coach_integration.py -q
```
