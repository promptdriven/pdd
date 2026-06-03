# CI Tiers

The public repository runs two default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.

`make regression-public` must remain safe for public forks. It must not require API keys, cloud authentication, Infisical, GCP, private repositories, or live LLM calls. Put live model and cloud checks in separate secret-gated workflows or in `pdd_cloud`, not in the default public PR path.

Longer suites remain separate:

- `make regression` and `make sync-regression` exercise LLM-backed CLI flows.
- `make cloud-regression` and cloud batch targets require cloud authentication and should run only in protected or private CI.

Projects with critical modules may add a **snapshot reproducibility** check that rejects unsnapshotted nondeterministic prompt context. Use **`pdd checkup snapshot`** only (there is no top-level `pdd policy` command). The check fails when a protected prompt uses `<shell>`, `<web>`, or `<include ... query="...">` without a replayable snapshot under `.pdd/evidence/`. Keep this separate from public fork-safe regression jobs if it requires private snapshot artifacts or secret-gated web access.

```bash
pdd checkup snapshot prompts/critical_python.prompt
```

The command exits non-zero when active nondeterministic tags are declared but `.pdd/evidence/` contains no replayable snapshot manifest for that prompt.

**`pdd checkup snapshot` vs `pdd checkup gate`:** `checkup snapshot` enforces that prompts declaring dynamic tags have a captured, replayable expanded-prompt manifest (from `pdd preprocess --snapshot` or `pdd generate|sync --snapshot-context`). `checkup gate` enforces dev-unit evidence policy (validation, contracts, cost limits) on `.pdd/evidence/devunits/*.latest.json`. Run both in protected CI when you use nondeterministic prompts and evidence receipts.

**Replay path:** `pdd replay` accepts the schema v1 snapshot manifest at `.pdd/evidence/runs/<run_id>.json` or an evidence manifest (schema v2) that links `context_snapshot.manifest_path`. Preprocess with `--snapshot` without `--recursive` when the prompt uses `<shell>` or `<web>` (recursive mode defers those tags).

## Compression Benchmark Gate

The compression benchmark gate (`pdd/compression_benchmark.py`) proves that context compression reduces token count without regressing pass rate or dropping required contract symbols. It is part of the parent epic #873 (deterministic context compression).

### Strategies compared

| Strategy | Description |
|---|---|
| `full_tests` | Raw test file, no compression |
| `ast_tests` | AST-sliced test file via `contract:` selector |
| `ast_contracts` | `ApiContractSlicer`-compressed source (seeds + transitive helpers) |
| `full_fewshot` | Full test file as few-shot usage example (no source implementation) |
| `compressed_fewshot` | AST-compressed source + AST-sliced tests |

### Metrics collected

Each strategy × fixture combination records:

- **Pass rate** — whether the generated (or simulated) output contains all required contract symbols.
- **Input tokens** — measured via `pdd.server.token_counter.count_tokens` before any LLM call.
- **Wall-clock time** — `time.perf_counter` around context build + (optional) LLM call.
- **Churn score** — `difflib.SequenceMatcher` ratio between expected and actual output (1.0 = identical).
- **Missing contracts** — symbols absent from output, detected by `ApiContractSlicer.verify_contract`.

### Hard-failure conditions

The gate returns exit code 1 when any of these conditions hold:

1. **Contract-symbol loss** — `missing_contracts` is non-empty for any result whose frozen baseline records `passed: true`. Strategies whose baseline records `passed: false` are comparison data points; a non-empty `missing_contracts` on those is expected and does not trigger the gate.
2. **Pass-rate regression** — a strategy's result is failing when the frozen baseline records it as passing.
3. **Churn below threshold** — churn score is below `PDD_COMPRESSION_CHURN_THRESHOLD` (default `0.90`) and below the fixture's own baseline.

### Frozen fixtures

Fixtures live under `tests/fixtures/compression_benchmark/`. Each subdirectory contains:

- `source.py` — module under test.
- `test_file.py` — test file for the module.
- `expected_output.py` — fallback frozen output used when no per-strategy file exists.
- `expected_output_{strategy}.py` — per-strategy frozen output files (one for each of `full_tests`, `ast_tests`, `ast_contracts`, `full_fewshot`, `compressed_fewshot`). These are the primary simulated LLM responses used in CI; they allow strategies that drop contract symbols (e.g. `ast_tests`, `full_fewshot`) to produce intentionally incomplete outputs so gate failures trigger correctly. `expected_output.py` is the fallback when a per-strategy file is absent.
- `contract_seeds.json` — list of required symbols that must survive compression.
- `expected_results.json` — per-strategy baselines (`passed`, `max_input_tokens`, `min_churn_score`).

At least one fixture (`contract_loss_regression/`) must have baselines showing that `ast_tests` and `full_fewshot` fail (missing contracts) while `ast_contracts` and `compressed_fewshot` pass. This directly covers the acceptance criterion requiring a fixture that previously failed without contract-source preservation.

### CI placement

Default CI (public fork-safe `unit-tests` job) runs the benchmark in **frozen-fixture mode** — no live LLM calls, fully deterministic. Live calls are opt-in:

```bash
pytest tests/test_compression_benchmark.py -m live_llm
```

Live-LLM tests require API credentials and are excluded from the public PR path. Place them in a secret-gated workflow alongside `make cloud-regression`.
