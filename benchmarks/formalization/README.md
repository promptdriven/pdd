# A0→A1 Prompt Formalization Benchmark (Milestone 1)

Benchmark for [issue #1273](https://github.com/promptdriven/pdd/issues/1273) / epic [#833](https://github.com/promptdriven/pdd/issues/833).

**M1 claim:** formalization improves **prompt checkability** (not code correctness or regen stability).

| Milestone | Name | Status |
|-----------|------|--------|
| **M1** | A0→A1 Prompt Formalization Benchmark | **This PR** |
| M2 | Formalized Prompt Generation Benchmark | Planned |
| M3 | Formalized Prompt Regeneration Stability Benchmark | Planned |

**Plan:** [PLAN.md](PLAN.md) · **Evaluation:** [EVALUATION.md](EVALUATION.md) · **Epic mapping:** [EPIC833.md](EPIC833.md)

## Quick eval — Milestone 1 (deterministic)

```bash
python benchmarks/formalization/pipelines/run_experiment.py
cat benchmarks/formalization/experiments/latest/REPORT.md
```

## Quick eval — full (M1 + v0.3 static harness)

```bash
bash benchmarks/formalization/scripts/run_eval.sh
```

## A0→A1 formalization script

Without product `pdd checkup lint --apply`, use the benchmark-local pipeline
(`formalize_script_v1` — pinned template, hashed, logged):

```bash
python benchmarks/formalization/pipelines/formalize_a1.py \
  --input  benchmarks/formalization/corpus/tasks/email_validator/A0.prompt \
  --output experiments/run_001/A1.prompt \
  --commands-log experiments/run_001/commands.jsonl
```

Add `--allow-llm` for LLM stages (experiment only; not CI).

## Corpus (M1)

Five handwritten A0 prompts under `corpus/tasks/` — see [corpus/manifest.yaml](corpus/manifest.yaml).

## v0.3 static harness (legacy)

```bash
python benchmarks/formalization/run_benchmark.py --report
```

See README sections below for arms, metrics, and tasks.

---

## Arms (v0.3 static harness)

| Arm | Name | What it measures |
|-----|------|------------------|
| **A0** | Ad-hoc prompt | Unstructured prompt prose |
| **A1** | PDD formalized | `<vocabulary>`, `<contract_rules>`, coverage |
| **A2** | Code-as-SOT | Reference implementation + pytest |

## Tests

```bash
pytest -vv tests/test_formalization_benchmark.py tests/test_formalization_pipeline.py
```
