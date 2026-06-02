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
| #825 Gate | CLOSED (CLI) | **Yes** | M1 checkup replay; `pdd checkup gate` (evidence + waiver policy); `tests/test_gate_main.py` |
| #826 Replay snapshot | OPEN | Partial | M2/M3 `--replay-fixtures`; tier_gold `pdd_generated/` |
| #827 Grounding provenance | OPEN | Partial | `<pin>` / `<exclude>` tags; manifest fixture |
| #828 Capabilities | OPEN | Partial | `<capabilities>` section present |
| #829 Prompt lint | CLOSED | Yes | `pdd checkup lint` via `scripts/cmd/pdd_checkup_lint.sh` |
| #830 Architecture metadata | OPEN | No | Placeholder (skipped) |
| #831 Drift | CLOSED (CLI) | **Yes** | M3 `run_m3_pipeline.py` + `scripts/cmd/pdd_drift.sh`; `tests/test_drift_main.py` |
| #832 Waivers | CLOSED (CLI) | **Yes** | `pdd checkup gate` waiver scan; coverage `waived` status |

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

## Post-merge verification (PR #1280)

After merging `main` into `feat/issue-1273-formalization-benchmark`:

```bash
bash benchmarks/formalization/scripts/touchpoint_pr1280.sh
```

This runs gate/drift/formalization unit tests, checks `pdd checkup gate` / `drift` CLI wiring, and the
no-LLM corpus smoke (`scripts/run_eval.sh`).

## Corpus milestone coverage (current)

| Milestone | Corpus tasks | Scripts |
|-----------|--------------|---------|
| **M1** checkability | 5 tasks (`corpus/manifest.yaml`) | `run_experiment.py`, `scripts/run_m1.sh`, per-task `EVALUATION_RESULT.md` |
| **M2** generate/test | tier A+B (`hello_fn`, `pi_digits`, `email_validator`, `token_bucket`, `refund_handler`) | `run_generation_benchmark.py`, `scripts/cmd/pdd_{generate,test}.sh` |
| **M3** drift | tier B with oracle (`email_validator`, `refund_handler`; `token_bucket` when M2 done) | `run_m3_pipeline.py`, `scripts/cmd/pdd_drift.sh` |

See [README.md](README.md), [COMMANDS.md](COMMANDS.md), and `experiments/latest/EVALUATION_RESULT.md` for recorded runs.
