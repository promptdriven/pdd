# Formalization benchmark baseline (v1)

Reference interpretation for `results/summary.json` and `results/REPORT.md`.

## TEF (Traceability + Enforceability + Fidelity)

Composite score in `[0, 1]` per arm. Weights (v1):

| Component | Weight | Source metric |
|-----------|--------|----------------|
| Rule coverage | 0.30 | `checked_rules / total_rules` |
| Story coverage | 0.15 | `(checked + story_only) / total_rules` |
| Test pass | 0.25 | `test_pass_rate` or test-only coverage proxy |
| Evidence | 0.10 | +0.10 if `evidence_manifest_present` |
| Lint clean | 0.10 | `1 - min(lint_warnings, 10)/10` |
| Formalization | 0.10 | `formal_candidate_rules / total_rules` |

Penalties:

- `-0.15 * (unchecked_rules / total_rules)`
- `-0.20` if `contract_check_errors > 0`

**A0 ad-hoc** with no `<contract_rules>` gets a small score from lint only (~0–0.10).

**A2** has no TEF (prompt metrics null by design).

## Primary comparison

**A0 → A1** is the product claim:

- More `total_rules`, `formal_candidate_rules`, `z3_test_count`
- Fewer `prompt_lint_warnings` (see `payment_api_lint`)
- Higher TEF

Do **not** require A1 to beat A2 on `test_pass_rate`; claim is traceability.

## Example headline (local run)

After `python benchmarks/formalization/run_benchmark.py --report`:

```text
email_validator: +6 contract rules (A0→A1); payment_api_lint: -N lint warnings (A0→A1)
```

## v1 artifacts

| File | Purpose |
|------|---------|
| `results/aggregate.json` | Raw per-arm runs |
| `results/summary.json` | Comparisons + TEF + deltas |
| `results/REPORT.md` | Markdown table for demos |

## Future (v1.1+)

- Gate compliance index (GCI) from `pdd checkup gate`
- Drift stability index (DSI) from `pdd checkup drift --runs 3`
- Lean/SMT calibration task
