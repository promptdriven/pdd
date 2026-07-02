# CI Tiers

The public repository runs three default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.
- `story-regression`: the user-story regression lane, `make regression-stories`, which runs `pytest -m story` with the deterministic/offline config and reports a per-story pass/fail summary (number of stories, number of story regression tests, per-story result). Like `public-cli-regression` it is fork-safe and runs with no API keys; it is non-blocking (reports only) — the merge-blocking coverage gate is tracked separately.

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

The story regression lane (`make regression-stories`) reports the executable
`@pytest.mark.story` suite's coverage deterministically (no LLM calls). It
prints a one-line summary to stdout and appends the same line to
`$GITHUB_STEP_SUMMARY`, while writing the durable machine-readable contract to
`.pdd/evidence/stories/coverage.latest.json` (schema:
`pdd/schemas/story_coverage.schema.json`) for upload as a build artifact.

```text
story regression: 142 tests across 96/110 stories (87% covered), 142 passing
```

The percentage is guarded against zero total stories (reported as
`not_applicable`, never `0%`). Trend is computed downstream in `pdd_cloud` from
the stateless per-run snapshots under `.pdd/evidence/stories/runs/`; this lane
emits snapshots only and does no trend math itself. See
[docs/evidence_manifest.md](evidence_manifest.md) for the artifact schema and
field definitions. Until the upstream story marker/lane/gate land, the lane
emits a `status: "not_applicable"` artifact rather than failing.
