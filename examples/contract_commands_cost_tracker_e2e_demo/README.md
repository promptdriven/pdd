# Contract commands E2E demo — cost_tracker

Demonstrates the deterministic **PDD contract command pipeline** applied to a real
prompt: the [`cost_tracker_utility_Python.prompt`](prompts/cost_tracker_utility_Python.prompt)
from `examples/template_example/`, plus a contracts-enriched variant
[`cost_tracker_with_contracts_python.prompt`](prompts/cost_tracker_with_contracts_python.prompt).

The demo shows the **before/after contrast** when a vague baseline prompt gains
structured `<contract_rules>`, `<vocabulary>`, and coverage evidence.

| Mode | Command | API? | What it shows |
|------|---------|------|----------------|
| **Deterministic** | `bash demo.sh` | No | `pdd prompt lint`, `pdd contracts check/compile`, `pdd coverage --contracts` on both prompts |

```bash
cd examples/contract_commands_cost_tracker_e2e_demo
bash demo.sh

# CI
pytest tests/test_contract_commands_cost_tracker_e2e_demo.py -q
```

---

## Prompts

| File | Role |
|------|------|
| `prompts/cost_tracker_utility_Python.prompt` | **Baseline** — verbatim copy from `template_example/`; no `<contract_rules>` |
| `prompts/cost_tracker_with_contracts_python.prompt` | **Contracts** — same spec + `<contract_rules>` / `<vocabulary>` / `<coverage>` |
| `prompts/cost_tracker_work_python.prompt` | Work copy used by ad-hoc clarify/compile experiments (not exercised by `demo.sh`) |

---

## What the deterministic flow does

For each prompt, runs the full deterministic pipeline:

```
① pdd prompt lint --json
② pdd contracts check --json --stories user_stories
③ pdd contracts compile --json
④ pdd coverage --contracts --json --stories-dir user_stories
```

**Outputs:** `reports/baseline.json`, `reports/contracts.json`, `reports/comparison.json`

**Expected contrast:**

| Metric | Baseline | Contracts |
|--------|----------|-----------|
| Has `<contract_rules>` | No (legacy-safe) | Yes |
| `contracts check` issues | 0 (no rules to check) | Low (well-formed) |
| `contracts compile` rules | 0 | ≥ 3 |
| Coverage (checked/story-only/unchecked) | — | R1/R2/R3 covered by story |

---

## Directory map

```
examples/contract_commands_cost_tracker_e2e_demo/
├── README.md
├── demo.sh
├── prompts/
│   ├── cost_tracker_utility_Python.prompt          # baseline (no contracts)
│   ├── cost_tracker_with_contracts_python.prompt   # contracts-enriched
│   └── cost_tracker_work_python.prompt             # work copy (manual experiments)
├── user_stories/
│   └── story__cost_tracker.md                      # covers R1, R2, R3
├── tests/
│   ├── test_cost_tracker_after.py                  # checked-in golden after-snapshot
│   ├── test_cost_tracker_before.py                 # checked-in golden before-snapshot
│   └── test_cost_tracker_reference.py              # reference suite used by demo.sh
├── lib/
│   └── run_e2e.py                                  # deterministic pipeline driver
└── reports/                                        # populated by demo.sh
    ├── baseline.json
    ├── contracts.json
    ├── comparison.json
    ├── artifacts/  (prompt + src + tests snapshots)
    └── diffs/      (prompt/src/tests unified diffs)
```

---

## See also

- [`examples/prompt_lint_contract_e2e_demo/`](../prompt_lint_contract_e2e_demo/) — vague vs formalized lint/contracts flow with live before/after codegen
- [`docs/contract_check.md`](../../docs/contract_check.md)
- [`docs/coverage_contracts.md`](../../docs/coverage_contracts.md)
