# Issue #830 verification touchpoints

Branch: `demo/issue-830-contract-summary-touchpoints`
Parent: `feat/issue-830-architecture-contract-summary`
PR: https://github.com/promptdriven/pdd/pull/1291

## One-liner

```bash
./examples/architecture_contract_summary_demo/run_demo.sh
```

## Acceptance matrix (#830)

| #830 criterion | Command / artifact |
|----------------|------------------|
| Legacy modules unchanged | `test_touchpoint_demo_sync_writes_contract_summary` (legacy has no `contract_summary`) |
| Sync from prompts/stories/evidence | Demo `refund_python.prompt` + `story__refund_cap.md` + `.pdd/evidence/.../refund_python.latest.json` |
| Malformed metadata → warnings | `test_update_architecture_contract_summary_warnings_on_read_errors` in `tests/test_architecture_sync.py` |
| Stable consumer fields | `pdd/schemas/architecture_contract_summary.schema.json`, `pdd/frontend/types.ts` |
| prompt / +story / +evidence / legacy tests | `tests/test_architecture_sync.py` + touchpoint file |
