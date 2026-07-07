# Experiment runner

Design.md §3.2 stages 3–5: sha-verified variant materialization, run
orchestration, metrics collection, and report generation. Runs are valid
without the optional FS tap (`fs_tap_enabled: false` in every record);
primary evidence comes from the context-snapshot tap.

## Pieces

| Module | Role |
|--------|------|
| `variant_builder.py` | materialize `(core, manifest)` → working repo; per-file sha256 verification; tree hash; hidden tree & manifest never copied in |
| `runner.py` | `ExperimentRunner` — freeze check (`manifests.lock`) → materialize → git baseline → proxy (+ mock provider) → agent → visible/hidden verification → attribution → trajectory → run record |
| `metrics.py` | design §6.3 run record: cost, penetration (usage-reconciled), H2 trajectory, edit classification (§6.2 precedence), §6.4 failure classes |
| `report.py` | per-size tables, pure-python least-squares + Spearman fits, failure breakdown, computed §7.5 threshold checklist |
| `mock_agent.py` | scripted agent + mock provider for **no-token** end-to-end pipeline validation (oracle / wrong_file / noop behaviors) |
| `cli.py` | `python3 -m harness.runner.cli --config experiment.json` |

## Quick demo (no network, no model tokens)

```bash
cd research/repo-bloat-benchmark
python3 -m pytest harness/runner/tests/ -q        # includes the e2e pipeline test
```

Or drive it by hand against the committed example scenario:

```bash
python3 -m harness.distractors.cli \
  --scenario-id example-pagination \
  --core scenarios/example-pagination/core \
  --pool scenarios/example-pagination/pool \
  --target-file src/pager/pagination.py \
  --sizes 1 2 5 --seed 1209 \
  --out /tmp/rb-distractors

cat > /tmp/rb-experiment.json <<'EOF'
{
  "scenario_dir": "scenarios/example-pagination",
  "distractors_dir": "/tmp/rb-distractors",
  "reports_dir": "/tmp/rb-reports",
  "work_root": "/tmp/rb-work",
  "arm": "mock",
  "mock_behavior": "oracle",
  "sizes": [1, 2, 5],
  "trials": 2
}
EOF
python3 -m harness.runner.cli --config /tmp/rb-experiment.json
cat /tmp/rb-reports/report.md
```

## Running a real agent arm

Set `"arm": "command"`, `"agent_command": ["codex", "exec", "--cd", "{workdir}", …]`
and `"upstream_base_url": "https://api.openai.com"`. The runner injects
`OPENAI_BASE_URL` pointing at the recording proxy; confirming the pinned
Codex build honors that override is the §10 pre-run blocker. The
run-environment freeze (§8.1.1 — pinned CLI, clean `CODEX_HOME`, ephemeral
session, egress locked to the proxy) is **not yet implemented** here and must
land before any real pilot run.
