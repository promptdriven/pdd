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
| `env_freeze.py` | §8.1.1 frozen agent environment: pinned CLI version, fresh per-run `CODEX_HOME` + generated config, sanitized allowlist env + egress guard, port-independent fingerprint, ephemeral collect-and-destroy |
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
Codex build honors that override is the §10 pre-run blocker.

### Run-environment freeze (design §8.1.1) — `env_freeze.py`

Real command-arm runs must set `RunConfig.freeze` (a `FreezeConfig`) and
should set `registered_env_fingerprint`. Per trial the runner then:

1. captures the CLI version and **aborts on any mismatch** with the pin;
2. creates a **fresh per-run `CODEX_HOME`** containing only a generated
   config (pinned model + reasoning effort, web search off, history
   persistence off, no MCP servers unless the arm enumerates them, and the
   recording proxy as the model provider);
3. runs the agent under a **sanitized allowlist environment** — the model API
   key is the only permitted secret — plus an **egress guard** (proxy vars
   black-hole all HTTP(S) except loopback, where the recording proxy
   listens);
4. verifies the built environment's **fingerprint** (port-independent sha256
   of the frozen combination) against the registered value, recording it as
   `env_fingerprint_sha256` in the run record (`null` ⇒ the run was not
   frozen and its numbers are development-only);
5. after the run, **archives** whatever the CLI wrote into its home
   (session logs feed the session-parser bypass cross-check) and **deletes
   the home** — ephemerality by destruction, not by trusting a flag.

The egress guard is the portable layer (honored by mainstream HTTP stacks,
not kernel enforcement); the Linux-container network lockdown remains the
hard tier for pilot runs, and session-log reconciliation detects bypass
either way. Exact Codex config key names are best-effort until the build is
pinned — the fingerprint covers the rendered config, so any adjustment is a
new registered environment by construction.
