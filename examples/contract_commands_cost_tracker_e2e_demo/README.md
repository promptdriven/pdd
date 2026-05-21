# Contract commands E2E demo (cost_tracker)

Exercises the **new deterministic contract commands** on the real
[`cost_tracker_utility_Python.prompt`](../../template_example/prompts/cost_tracker_utility_Python.prompt)
from `examples/template_example/` (copied verbatim), plus a contracts-enriched variant
for coverage and drift.

| Mode | Command | API? | What it proves |
|------|---------|------|----------------|
| **Deterministic** | `bash demo.sh` | No | `pdd gate`, `pdd evidence emit/validate`, `pdd contracts drift`, `pdd contracts author` (no LLM) |
| **Live** | `bash demo.sh --live` | Yes | `pdd contracts author --apply` on work copy |

```bash
cd examples/contract_commands_cost_tracker_e2e_demo
bash demo.sh

# CI
pytest tests/test_contract_commands_cost_tracker_e2e_demo.py -q
```

## Prompts

| File | Role |
|------|------|
| `prompts/cost_tracker_utility_Python.prompt` | Verbatim copy from template_example |
| `prompts/cost_tracker_with_contracts_python.prompt` | Same spec + `<contract_rules>` / `<vocabulary>` for gate & coverage |

## Deterministic flow (`lib/run_e2e.py`)

```text
① pdd gate + pdd evidence emit/validate  (baseline prompt)
② pdd gate + pdd evidence emit            (contracts prompt)
③ pdd contracts drift                     (baseline vs contracts manifests)
④ pdd contracts author                    (run_llm_clarify=False — no API)
⑤ pdd contracts drift                     (contracts vs work manifest)
```

**Outputs:** `reports/comparison.json`, `reports/gate_*.json`, `reports/evidence_*.json`, `reports/drift.json`

## Live flow

```bash
export PDD_SKIP_UPDATE_CHECK=1
pdd auth status   # or API keys
bash demo.sh --live --keep-artifacts
```

Runs `pdd contracts author --apply --non-interactive` on the contracts prompt work copy.

## Reference implementation

`src/edit_file_tool/cost_tracker_utility.py` is copied from template_example for local
pytest and optional `pdd test --contracts` experiments (not required for deterministic demo).

## See also

- [`examples/prompt_lint_contract_e2e_demo/`](../prompt_lint_contract_e2e_demo/) — vague vs formalized lint/contracts flow
- [`docs/gate.md`](../../docs/gate.md) — three-layer architecture
