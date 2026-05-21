# Contract authoring in `.prompt` files

Prompt contracts are a **requirements system** inside `.prompt` files. A rule is
considered formal only when it has:

- stable ID (`R1`, `R-001`, …)
- modal verb (`MUST`, `MUST NOT`, …)
- observable behavior
- defined terms in `<vocabulary>` (when using vague words)
- coverage or an active waiver
- optional approved `<formalization>` (future verification)

## Core sections

```xml
<contract_rules>
R1 - Reject zero refund
When amount_cents is 0,
the service MUST return HTTP 400 and MUST NOT call provider_client.
</contract_rules>

<vocabulary>
reject: Return an error and do not perform the operation.
</vocabulary>

<coverage>
R1: story__refund_invalid.md, test_R1_rejects_zero_refund
R2: WAIVED W1
</coverage>

<waivers>
W1:
  Rule: R2
  Reason: Legacy API limitation.
  Approved by: maintainer
  Expires: 2026-08-01
</waivers>
```

## Shared IR

All contract commands parse via [`pdd/contract_ir.py`](../pdd/contract_ir.py)
(`pdd.prompt_contract_ir.v1`):

```bash
pdd contracts compile --authoring --json prompts/foo_python.prompt
```

## Command layers

| Layer | Command | CI |
|-------|---------|-----|
| Clarity | `pdd prompt lint` | deterministic |
| Structure | `pdd contracts check` | yes |
| Evidence | `pdd coverage --contracts` | yes |
| Advisory | `pdd contracts review --llm` | no |
| Obligations IR | `pdd contracts compile` | yes |

## Formalization (stub)

```xml
<formalization>
R1:
  level: property
  target: smt
  predicate: amount <= 0 => result.status == "rejected"
  status: draft
</formalization>
```

Verification backends (`formalize`, `verify`) are planned follow-up work.
