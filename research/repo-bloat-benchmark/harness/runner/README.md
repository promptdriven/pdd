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
and `"upstream_base_url": "https://api.openai.com"`. Command-arm runs require
`RunConfig.freeze`; set `allow_unfrozen_command=true` only for harness
development, never for pilot data. The runner routes the agent through the
recording proxy via the generated frozen config's `model_providers` block
(plus `OPENAI_BASE_URL`); that the pinned build honors this override is
**confirmed** for `codex-cli 0.142.4` — see `CODEX_PIN.md` and
`python3 -m harness.runner.codex_probe`, a zero-billing probe you can rerun
against any candidate build before re-pinning. Nonzero agent exits abort the
trial before a benchmark record is written and leave `agent_process.json`
for diagnosis.

Scenario verifier commands and command-arm `agent_command` entries may use
`"{workdir}"` for the materialized variant and `"{python}"` for the Python
interpreter running the harness. Use `"{python}"` for committed Python
scenario tests so local verification does not depend on whichever `python3`
appears first on `PATH`.

### Run-environment freeze (design §8.1.1) — `env_freeze.py`

Real command-arm runs must set `RunConfig.freeze` (a `FreezeConfig`) and
`registered_env_fingerprint`, unless explicitly marked as harness-development
with `allow_unfrozen_command=true`. Per trial the runner then:

1. captures the CLI version and **aborts on any mismatch** with the pin;
2. creates a **fresh per-run `CODEX_HOME`** containing only a generated
   config (pinned model + reasoning effort, web search off, history
   persistence off, no MCP servers unless the arm enumerates them, and the
   recording proxy as the model provider);
3. runs the agent under a **sanitized allowlist environment** — `HOME` is
   redirected to the fresh per-run home and the model API key is the only
   permitted secret — plus an **egress guard** (proxy vars black-hole all
   HTTP(S) except loopback, where the recording proxy listens);
4. verifies the built environment's **fingerprint** (port-independent sha256
   of the frozen combination) against the registered value, recording it as
   `env_fingerprint_sha256` in the run record (`null` ⇒ the run was not
   frozen and its numbers are development-only);
5. after the run, **archives** whatever the CLI wrote into its home, including
   final `config.toml` bytes (session logs feed the session-parser bypass
   cross-check), and **deletes the home** — ephemerality by destruction, not by
   trusting a flag.

The egress guard is the portable layer (honored by mainstream HTTP stacks,
not kernel enforcement); the Linux-container network lockdown remains the
hard tier for pilot runs, and session-log reconciliation detects bypass
either way. Exact Codex config key names are best-effort until the build is
pinned — the fingerprint covers the rendered config, so any adjustment is a
new registered environment by construction.
