# Epic #833 → benchmark mapping

Parent: [issue #833](https://github.com/promptdriven/pdd/issues/833) — language-complete PDD (prompts + contracts + stories + tests + evidence).

Benchmark: [issue #1273](https://github.com/promptdriven/pdd/issues/1273).

## Source-set questions (epic)

Each **A1 formalized** run produces `epic833` in result JSON answering:

| Epic question | Benchmark signal | Issues |
|---------------|------------------|--------|
| What does this module intend? | `total_rules` > 0, `<vocabulary>` | #833 |
| What contracts must it satisfy? | `contract_check_errors` == 0 | #822 |
| Which stories cover those contracts? | `stories_with_covers`, coverage `story_only` | #820, #823 |
| Which tests execute those contracts? | `rule_id_test_functions`, `test_only` | #821, #823 |
| Which checks passed? | `command_success`, lint/contract counts | #829, #822 |
| Which claims are unchecked or waived? | `unchecked_rules`, `waived_rules` | #832, #823 |
| Could this generation be replayed or audited? | `evidence_manifest_present`, grounding tags | #824, #827, #826 |

## Sub-issue coverage in benchmark

| Issue | State | Measured in benchmark? | How |
|-------|-------|------------------------|-----|
| #820 Story template | OPEN | Partial | Count `## Covers` / `## Oracle` in stories |
| #821 Tests from rule IDs | OPEN | Partial | Count `test_R*` functions |
| #822 Contract check | CLOSED | Yes | `pdd.contract_check` via runner |
| #823 Coverage matrix | CLOSED | Yes | `pdd.coverage_contracts` |
| #824 Evidence manifest | CLOSED | Partial | `evidence_paths` in task.yaml |
| #825 Gate | OPEN | CLI probe only | `gate_main` import; manual `pdd checkup gate` |
| #826 Replay snapshot | OPEN | No | Placeholder check (skipped) |
| #827 Grounding provenance | OPEN | Partial | `<pin>` / `<exclude>` tags; manifest fixture |
| #828 Capabilities | OPEN | Partial | `<capabilities>` section present |
| #829 Prompt lint | CLOSED | Yes | `pdd.prompt_lint` |
| #830 Architecture metadata | OPEN | No | Placeholder (skipped) |
| #831 Drift | OPEN | CLI probe only | `drift_main` import; manual drift |
| #832 Waivers | OPEN | Partial | `waived_rules` from coverage |

## Hero tasks for epic demo

| Task | Best for |
|------|----------|
| `refund_payment` | Full source set: rules, stories, Covers, tests, waivers, capabilities |
| `email_validator` | Formalization + Z3 + pytest baseline |
| `payment_api_lint` | #829 vague vs defined vocabulary (A0 vs A1 lint delta) |

Run the scorecard:

```bash
jq '.epic833' benchmarks/formalization/results/refund_payment/A1.json
```
