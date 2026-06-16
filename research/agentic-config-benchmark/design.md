# Design: Agentic CLI Config Benchmark Axis

**Issue:** [#1594](https://github.com/promptdriven/pdd/issues/1594) — Agentic CLI routing: benchmark axis and config data
**Parent:** [#1585](https://github.com/promptdriven/pdd/issues/1585)
**Related:** [#1209](https://github.com/promptdriven/pdd/issues/1209), [#1419](https://github.com/promptdriven/pdd/issues/1419), [#1431](https://github.com/promptdriven/pdd/issues/1431), [#1430](https://github.com/promptdriven/pdd/issues/1430)
**Status:** Draft — **§8 decisions LOCKED** (axis definition, schema extension, Wilson CI, N=5, 30-min timeout, default baseline anchor)
**Last updated:** 2026-06-15

---

## 1. Purpose and research question

**Research question.** Does varying the agentic CLI configuration — harness, model, thinking mode, and repeat-run count — produce meaningfully different pass-rate, cost, latency, and failure-class outcomes on the same fixed task suite?

Operationalized:

> Given a fixed set of tasks (fixed task brief, seed, visible tests, hidden verifier, materialized repo, and timeout policy), what happens to `hidden_pass_rate`, `cost_usd_median`, `wall_clock_seconds_p50`, `wrong_file_edit_rate`, `files_read_before_first_edit_p50`, `timeout_rate`, and primary `failure_class` as we vary `(harness_id, harness_version, model_id, thinking_enabled, thinking_effort)` — the config identity — while holding everything else constant?

The benchmark extends the `#1209` / `#1419` agentic-column axis to support a **config sweep**: each candidate config is a distinct column, all sharing identical task fixtures, locked content hashes, and timeout settings.

**What this is not.** This is a **within-task, between-config** comparison, not a new task design effort. Tasks come from `#1419`; the hidden verifier is opaque infrastructure. This study answers "which config performs better on the same tasks," not "which tasks discriminate better."

---

## 2. Design principles

- **Determinism before runs.** Task fixtures (visible tests, hidden verifier, materialized repo) are content-addressed (SHA256) and committed before any model invocation. A run references these by hash; a changed hash is a new experiment.
- **One thing varies.** Within a sweep, the **config identity** — `(harness_id, harness_version, model_id, thinking_enabled, thinking_effort)` — is the only variable. Task, seed, visible tests, hidden verifier, materialized repo, and `timeout_seconds` are byte-identical across all config cells.
- **Hidden success is the verdict.** A visible-test pass with a hidden-verifier failure is a failure. `hidden_pass_rate` is the primary outcome metric.
- **Interactive-only models are excluded.** Models with `interactive_only=True` in `pdd/data/llm_model.csv` require device-flow OAuth or running local servers and hang in non-interactive contexts. They are skipped before scheduling any cell.
- **Thinking cells are model-gated.** A `thinking=True` config cell is only scheduled for models where `reasoning_type` is `"effort"` or `"budget"` (i.e., models that expose a thinking/reasoning budget control). For other models, `thinking=True` cells are skipped with a warning.
- **Reproducible by a third party.** JSONL run records, axis definition, and the analysis script must let an external evaluator re-derive every table from raw logs.

---

## 3. Config identity

Each config cell is identified by a canonical SHA256 computed over a deterministic JSON representation of its config fields:

```python
import hashlib, json

def config_sha256(harness_id: str, harness_version: str, model_id: str,
                  thinking_enabled: bool, thinking_effort: str | None) -> str:
    canonical = json.dumps({
        "harness_id": harness_id,
        "harness_version": harness_version,
        "model_id": model_id,
        "thinking_enabled": thinking_enabled,
        "thinking_effort": thinking_effort,
    }, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()
```

`config_sha256` is the stable groupby key for aggregating JSONL records into per-config cells in the report. The `is_default_baseline` flag marks the anchor row.

---

## 4. Axis definition (`benchmark_config_axis.json`)

### 4.1 Locked invariants

Before any run, the following must be committed in `benchmark_config_axis.json`:

| Field | Description |
|-------|-------------|
| `task_id` | Task identifier (from `#1419`) |
| `seed` | Fixed task seed / fixture seed used for every config cell |
| `visible_tests_sha256` | SHA256 of the visible test fixture tree |
| `hidden_verifier_sha256` | SHA256 of the hidden verifier tree (opaque; harness-only) |
| `materialized_repo_sha256` | SHA256 of the materialized base repo used for all cells |
| `timeout_seconds` | Timeout per run — **byte-identical across all cells in a sweep** |
| `repeat_runs` | Number of trial replicates per `(task, config)` cell |

A run that finds any locked hash field still set to a placeholder value aborts before spending any model tokens.

### 4.2 Config cells

The initial sweep defines **six config cells** spanning the key axes (model strength, thinking mode). Cells are ordered by `config_rank` (lower = weaker / cheaper); the default baseline is anchored at rank 0.

| Rank | Label | `model_id` | `thinking_enabled` | `thinking_effort` | `is_default_baseline` |
|------|-------|-----------|-------------------|------------------|----------------------|
| 0 | baseline | `anthropic.claude-sonnet-4-6` | false | null | **true** |
| 1 | baseline+thinking | `anthropic.claude-sonnet-4-6` | true | `"medium"` | false |
| 2 | stronger | `anthropic.claude-opus-4-7` | false | null | false |
| 3 | stronger+thinking | `anthropic.claude-opus-4-7` | true | `"medium"` | false |
| 4 | latest | `anthropic.claude-opus-4-8` | false | null | false |
| 5 | latest+thinking | `anthropic.claude-opus-4-8` | true | `"medium"` | false |

**Model selection rationale.** Candidate models are drawn from `pdd/data/llm_model.csv` filtered to `interactive_only=False`. The three selected models (ranked by `model_rank_score` from `deepswe-solve-rate` or `static-prefix` sources):

| `model_id` | `model_rank_score` | `model_rank_source` | `reasoning_type` |
|---|---|---|---|
| `anthropic.claude-opus-4-8` | 1575 | static-prefix | effort |
| `anthropic.claude-sonnet-4-6` | 13200 | deepswe-solve-rate | effort |
| `anthropic.claude-opus-4-7` | 15400 | deepswe-solve-rate | effort |

All three have `reasoning_type=effort`, making `thinking=True` cells valid for each.

**DeepSWE evidence.** For cells using `anthropic.claude-opus-4-7` and `anthropic.claude-sonnet-4-6`, `model_rank_score` reflects a DeepSWE solve-rate rank rather than raw arena ELO. The report surfaces this as `external_deepswe_rank_score` with an explicit harness-bundling caveat: DeepSWE solve-rate is measured under a different harness setup than the PDD agentic CLI harness, so the scores inform model-strength ordering but do not translate directly to PDD pass-rate predictions.

---

## 5. Run record schema

One JSONL line per `(task_id, config_sha256, trial_index)` run:

```json
{
  "run_id": "task-alpha.3a7f9b...trial0.2026-06-15T00:00:00Z",
  "schema_version": 1,
  "task_id": "task-alpha",
  "config_sha256": "3a7f9b...",
  "trial_index": 0,
  "repeat_run_index": 0,

  "harness_id": "pdd-agentic-cli",
  "harness_version": "1.0.0",
  "model_id": "anthropic.claude-sonnet-4-6",
  "thinking_enabled": false,
  "thinking_effort": null,
  "is_default_baseline": true,

  "model_rank_score": 13200,
  "model_rank_source": "deepswe-solve-rate",
  "reasoning_type": "effort",
  "external_deepswe_rank_score": 13200,
  "deepswe_rank_caveat": "Measured under DeepSWE harness; not directly comparable to PDD agentic CLI pass-rate.",

  "task_id_locked": "task-alpha",
  "seed_locked": "seed-alpha",
  "visible_tests_sha256": "...",
  "hidden_verifier_sha256": "...",
  "materialized_repo_sha256": "...",
  "timeout_seconds": 1800,
  "repeat_runs": 5,
  "hash_verified": true,

  "hidden_pass": false,
  "visible_pass": false,
  "failure_class": null,

  "cost_usd": null,
  "cost_source": "provider_usage_api",
  "input_tokens": 0,
  "output_tokens": 0,
  "wall_clock_seconds": 0.0,
  "timed_out": false,

  "files_read_before_first_edit": 0,
  "files_read_source": "fs_tap",
  "wrong_file_edit_count": 0,

  "raw_trace_path": "reports/<run_id>/trace.jsonl"
}
```

### 5.1 Field notes

- `config_sha256` — stable groupby key computed from `(harness_id, harness_version, model_id, thinking_enabled, thinking_effort)`; see §3.
- `cost_source` — one of `"provider_usage_api"` (from live `usage` object), `"estimated_from_tokens"` (token-based estimate when live usage is unavailable), or `"unavailable"` (neither source accessible).
- `files_read_source` — one of `"fs_tap"` (FUSE/OverlayFS byte-extent tap), `"transcript_tap"` (tool-call log), or `"unavailable"`.
- `hidden_pass: null` — recorded when the hidden verifier is not available in the execution context. `hidden_pass_rate` is omitted from the report (not fabricated) for any config cell where all trials yield `null`.
- `failure_class` — one of: `wrong_file_edit`, `localization_miss`, `context_overflow`, `timeout`, `hidden_contract_miss`, `forbidden_access`, `other`. Null on hidden pass.
- `deepswe_rank_caveat` — always recorded when `model_rank_source` is `"deepswe-solve-rate"`, to surface the harness-bundling caveat in both the run record and the report.

### 5.2 Failure classification

Inherits the taxonomy from `research/repo-bloat-benchmark/design.md §6.4`:

| Class | Definition |
|-------|-----------|
| `wrong_file_edit` | Agent edited outside the allowed scope |
| `localization_miss` | Never read the target file before exhausting attempts |
| `context_overflow` | Hit a context/window limit |
| `timeout` | Exceeded `timeout_seconds` |
| `hidden_contract_miss` | Visible tests pass but hidden verifier fails |
| `forbidden_access` | Read/edited the hidden tree or a prohibited path |
| `other` | Free-text note required; should be rare |

---

## 6. Replication

Each `(task_id, config_sha256)` cell is run over **`N = 5` replicates** (`trial_index` 0–4), matching the `research/repo-bloat-benchmark` pilot. With 6 config cells and `M` tasks, the total run count is `M × 6 × 5`.

`N = 5` is a **pilot** sample chosen to surface effect sizes and variance, not to power a significance test. The report is therefore **descriptive/directional** (see §7.5); a power/effect-size calculation that sets `N` for a confirmatory follow-up is an explicit deliverable, not a claim made from pilot data.

---

## 7. Reporting format

### 7.1 Per-config summary table

One row per config cell (`config_sha256`), one column per metric, ordered by `config_rank`:

| Config | `hidden_pass_rate` (k/N ± Wilson CI) | `cost_usd_median` | `wall_clock_s_p50` | `timeout_rate` | `wrong_file_edit_rate` | `files_read_p50` | `primary_failure_class` | `deepswe_rank_score` | `delta_hidden_pass_vs_baseline` |
|--------|---|---|---|---|---|---|---|---|---|
| baseline | | | | | | | | | — |
| baseline+thinking | | | | | | | | | ± pp |
| stronger | | | | | | | | | ± pp |
| stronger+thinking | | | | | | | | | ± pp |
| latest | | | | | | | | | ± pp |
| latest+thinking | | | | | | | | | ± pp |

`delta_hidden_pass_vs_baseline` = `hidden_pass_rate` minus the baseline row's `hidden_pass_rate`.

### 7.2 Interval method

- **Rate metrics** (`hidden_pass_rate`, `visible_pass_rate`, `wrong_file_edit_rate`, `timeout_rate`): **Wilson score intervals** (appropriate for small binomial counts with `N = 5`) plus raw `k/N`.
- **Continuous metrics** (`cost_usd`, `wall_clock_seconds`, `files_read_before_first_edit`): median and min–max range. No normal-theory CI on 5 points.

### 7.3 DeepSWE evidence column

For cells where `model_rank_source` is `"deepswe-solve-rate"`, the report includes `external_deepswe_rank_score` in the summary table with a **harness-bundling caveat footnote**:

> DeepSWE solve-rate scores are measured under the DeepSWE harness setup, not the PDD agentic CLI harness. They indicate model-strength ordering but do not translate directly to PDD pass-rate predictions. Cells using this score: `stronger`, `stronger+thinking`, `baseline+thinking`, `baseline`.

### 7.4 Methodology note

A short prose section recording:

- what was held constant vs varied
- model metadata source (`pdd/data/llm_model.csv`) and the `interactive_only` exclusion rule
- `thinking` cell scheduling logic (only for `reasoning_type=effort|budget` models)
- how locked hashes were verified before each run
- `cost_source` and `files_read_source` provenance per config cell
- `hidden_pass: null` handling (cells omitted from `hidden_pass_rate` if all trials are null)
- replicate count and how dispersion was reported
- the DeepSWE harness-bundling caveat

### 7.5 Conclusion (required, pre-committed interpretation)

**Pre-registered practical thresholds** (fixed before any run):

| Metric | Threshold for "notable difference" (vs baseline) |
|--------|-------------------------------------------------|
| `hidden_pass_rate` | ≥ **15 percentage-point** absolute change |
| `cost_usd_median` | ≥ **2×** or ≤ **0.5×** the baseline median |
| `wall_clock_seconds_p50` | ≥ **1.5×** or ≤ **0.67×** the baseline p50 |
| `timeout_rate` | ≥ **0.20** absolute |
| `wrong_file_edit_rate` | ≥ **0.20** absolute |

The report must state in plain language whether each config:

- **outperforms** the baseline — `hidden_pass_rate` delta ≥ +15 pp with no worse cost/timeout/wrong-edit trade-off crossing threshold;
- **underperforms** the baseline — `hidden_pass_rate` delta ≤ −15 pp;
- **is cost-equivalent** — within threshold on `hidden_pass_rate` but notably cheaper or faster;
- **is inconclusive** — replicate dispersion is large relative to the effect;
- **is not recommended** — `hidden_pass_rate` similar or worse *and* cost/latency/wrong-edit rate crosses a threshold in the wrong direction.

Because the pilot is descriptive, the conclusion motivates (and sizes) a powered confirmatory study, not a significance verdict.

---

## 8. Locked decisions

Frozen before any model run.

| # | Decision | Locked choice |
|---|----------|---------------|
| 1 | Config identity hash | SHA256 over `{harness_id, harness_version, model_id, thinking_enabled, thinking_effort}` (canonical JSON, `sort_keys=True`) |
| 2 | Default baseline anchor | `anthropic.claude-sonnet-4-6`, `thinking=False`, `harness_id="pdd-agentic-cli"` |
| 3 | Replicates per `(task, config)` | **N = 5** (`trial_index` 0–4) |
| 4 | Per-run timeout | **1800 s (30 min)** — byte-identical across all cells |
| 5 | Rate metric interval | **Wilson score CI** (not normal-theory CI) |
| 6 | Model exclusion rule | `interactive_only=True` rows in `pdd/data/llm_model.csv` are never scheduled |
| 7 | Thinking-cell gate | `thinking=True` cells only for `reasoning_type ∈ {"effort", "budget"}` |
| 8 | Hidden-null policy | `hidden_pass: null` → config row omitted from `hidden_pass_rate` (not fabricated) |

---

## 9. Relationship to `research/repo-bloat-benchmark`

This benchmark **does not** reproduce the repo-bloat axis. It reuses:

- The **run record schema fields** from `research/repo-bloat-benchmark/design.md §6.3` as a base — `hidden_pass`, `visible_pass`, `failure_class`, `files_read_before_first_edit`, `wrong_file_edit_count`, `wall_clock_seconds`, `input_tokens` — extended with config-identity fields (`config_sha256`, `is_default_baseline`, `model_id`, `thinking_enabled`, `thinking_effort`, `cost_usd`, `cost_source`, `files_read_source`, `external_deepswe_rank_score`).
- The **failure taxonomy** verbatim.
- The **N = 5 replicate** and **30-min timeout** decisions.
- The **Wilson CI** convention for rate metrics.

The repo-bloat benchmark varies distractor volume on a fixed config; this benchmark varies config on fixed tasks. They are complementary axes.

---

## 10. Directory layout

```
research/agentic-config-benchmark/
  design.md                        ← this document
  benchmark_config_axis.json       ← sweep definition: config cells + locked fixture hashes
  run_benchmark.py                 ← matrix runner: iterates (task, config, trial_index)
  generate_report.py               ← report generator: JSONL → Markdown summary table
  reports/                         ← output directory for per-run JSONL records and reports
    .gitkeep
```

---

## 11. Out of scope

- Running direct `llm_invoke` benchmark cells; see [#1584](https://github.com/promptdriven/pdd/issues/1584).
- Tuning tasks after seeing model outputs.
- Sourcing or generating task fixtures (those come from [#1419](https://github.com/promptdriven/pdd/issues/1419)).
- Modifying `pdd/` core modules — all changes are additive research artifacts in `research/`.
