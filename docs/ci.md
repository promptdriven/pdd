# CI Tiers

The public repository runs three default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.
- `story-regression`: the user-story regression lane, `make regression-stories`, which runs `pytest -m story` with the deterministic/offline config and reports a per-story pass/fail summary (number of stories, number of story regression tests, per-story result) via the `pytest_terminal_summary` hook in `tests/conftest.py`. Like `public-cli-regression` it is fork-safe and runs with no API keys. It is **blocking**: a failing or stale story test fails the job (the generated tests hard-assert the story hash, and the lane has no `continue-on-error`). An empty suite (no `@pytest.mark.story` tests collected) is treated as a green no-op.

Both `make regression-public` and `make regression-stories` must remain safe for public forks. They must not require API keys, cloud authentication, Infisical, GCP, private repositories, or live LLM calls. Put live model and cloud checks in separate secret-gated workflows or in `pdd_cloud`, not in the default public PR path.

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

## Story Regression Coverage

What the `story-regression` job does **today** is run the executable
`@pytest.mark.story` suite (`make regression-stories` → `pytest -m story`) and
fail on any failing or stale story. This is a pass/fail gate — it does not yet
emit a machine-readable coverage artifact.

The deterministic (no-LLM) coverage emitter is a **library capability that CI
does not yet invoke.** `pdd/story_coverage.py` can compute a `StoryCoverage`
result, print a one-line summary, append it to `$GITHUB_STEP_SUMMARY`, and write
the durable contract to `.pdd/evidence/stories/coverage.latest.json` (schema:
`pdd/schemas/story_coverage.schema.json`) plus a per-run snapshot under
`.pdd/evidence/stories/runs/`. Its shape is:

```text
story regression: 142 tests across 96/110 stories (87% covered), 142 passing
```

But nothing in the CI path calls it: `make regression-stories` /
`tests/story_regression.sh` only run `pytest -m story`, and the `story-regression`
job writes no summary line, no JSON, and uploads no artifact. The only in-tree
caller is the demonstration script `context/story_coverage_example.py`. Wiring
the emitter into the lane (the summary line, the `coverage.latest.json` upload,
and the pass/fail + freshness verdicts that let it emit `status: "ok"` or an
honest failure instead of the current `status: "not_applicable"`,
`pass_rate: null`, `passing_test_count: 0`) is tracked in issue #1909.

Until then, treat the coverage artifact the way
[docs/evidence_manifest.md](evidence_manifest.md) describes it — a schema-versioned
contract with a `not_applicable` degraded mode — and read that document for the
field definitions. Trend is computed downstream in `pdd_cloud` from the stateless
per-run snapshots once the lane emits them; the emitter itself does no trend math.
