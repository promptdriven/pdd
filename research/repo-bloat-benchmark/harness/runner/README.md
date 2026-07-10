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
trial no longer kill the cell; they are recorded as `agent_error` in the run
record and leave `agent_process.json` for diagnosis. For the Docker hard
tier, set `"agent_launcher": "container_worker"` and
`"agent_request_dir"` to a path shared with the `agent` service so the real
Codex process executes inside the isolated agent namespace while still
writing its frozen `CODEX_HOME` under the shared reports volume.
`harness.runner.container.integration_check` is the no-billing smoke for that
path: it launches the command arm through the isolated worker, verifies the
advertised proxy host is `runner`, confirms the gateway is unreachable from
the agent namespace, and checks the shared frozen-home artifacts land in the
report directory.

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
either way. Codex config key names are validated against the pinned build
(`CODEX_PIN.md`) — the fingerprint covers the rendered config, so any
adjustment is a new registered environment by construction.

## Pre-run gates (design §4.1.2 + §6.6) — `preflight.py`

Before any model run, the same experiment config the pilot will use must
pass:

```bash
python3 -m harness.runner.preflight --config experiment.json --json preflight.json
```

- **Oracle-equivalence sweep** — for every `(scenario, size)` on the ladder:
  manifest verified against `manifests.lock`, variant materialized, hidden
  tree asserted absent, core files asserted byte-identical to the 1x core,
  baseline invariant (visible PASS / hidden FAIL), oracle invariant (after
  `oracle_edit`: visible PASS / hidden PASS), with the runtime fingerprint
  recorded per cell.
- **Instrumentation calibration** — proxy fidelity against fixed fixtures in
  both wire shapes (Responses SSE and chat-completions JSON): byte-exact
  archive, sha256 fidelity, `usage` extraction, edit-tool-call detection.
  FS-tap assertions apply only when that tier is enabled (it is not).

Exit code 0 iff every gate passes; zero model tokens.
