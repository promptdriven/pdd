# Architecture `contract_summary` demo (issue #830)

Self-contained mini-project showing how `pdd sync-architecture` populates
`contract_summary` on each `architecture.json` module from prompts, user stories,
and devunit evidence manifests.

## Quick verify (from repository root)

```bash
# Automated touchpoint (pytest)
pytest -vv tests/test_issue_830_contract_summary_touchpoint.py

# Interactive terminal demo
./examples/architecture_contract_summary_demo/run_demo.sh
```

## What the demo exercises

| Scenario | Module | Expected |
|----------|--------|----------|
| Prompt + story + fresh evidence | `refund_python.prompt` | `rules`, `story-only`/`partial`, `evidence_status: fresh` |
| Legacy (no contracts) | `legacy_python.prompt` | No `contract_summary` key written |

## Manual steps

```bash
cd examples/architecture_contract_summary_demo

# Dry-run (no write)
python run_demo.py --dry-run

# Apply sync and print summaries
python run_demo.py

# Inspect architecture.json
python -c "import json; print(json.dumps(json.load(open('architecture.json'))[0].get('contract_summary'), indent=2))"
```

## Branch

This example is maintained on
`demo/issue-830-contract-summary-touchpoints` (child of
`feat/issue-830-architecture-contract-summary`) for human QA alongside
[promptdriven/pdd#1291](https://github.com/promptdriven/pdd/pull/1291).
