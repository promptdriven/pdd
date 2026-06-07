# PDD Checkup Verifier Namespace

`pdd checkup` is PDD's **verifier namespace**: one entry point for prompt
source-set health, focused deterministic checks, and GitHub issue/PR review.

## Prompt source-set health

Run a unified report before generating or changing code:

```bash
pdd checkup prompts/foo_python.prompt
pdd checkup prompts/
pdd checkup refund_payment
```

See [checkup_prompt_quality_gate.md](checkup_prompt_quality_gate.md) for the
automatic gate, report schema, and workflow hooks.

## Focused checks (CI / debugging)

| Command | Doc |
|---------|-----|
| `pdd checkup lint` | [prompt_lint.md](prompt_lint.md) |
| `pdd checkup contract check` | [contract_check.md](contract_check.md) |
| `pdd checkup coverage` | [coverage_contracts.md](coverage_contracts.md) |
| `pdd checkup gate` | [evidence_manifest.md](evidence_manifest.md) |
| `pdd checkup snapshot` | snapshot policy for nondeterministic tags |
| `pdd checkup drift` | [drift.md](drift.md) |

## Issue / PR checkup

```bash
pdd checkup https://github.com/org/repo/issues/123
pdd checkup --pr https://github.com/org/repo/pull/123
```

These modes are unchanged from the agentic checkup workflow.
