# Pre-registered pilot-arm values (design §10 — frozen 2026-07-07)

The mechanics behind every value below were verified without billing by the
routing probe (`CODEX_PIN.md`). These are the **frozen numeric/identity
choices** the design left as human pre-registration decisions; they were
frozen by the experiment owner on 2026-07-07 (delegated in-session), are
committed in `pilot_arm_codex.json`, and are covered by the env fingerprint
— **changing any of them is a new experiment, not a variant** (§10).

| Field | Frozen value | Rationale |
|---|---|---|
| CLI | `codex-cli 0.142.4` | the probe-verified build (`CODEX_PIN.md`); no auto-update — a re-pin re-runs the probe first |
| `model_id` | `gpt-5.1-codex-max` | the flagship coding model of the pinned CLI generation; agentic-coding default for this CLI |
| `reasoning_effort` | `medium` | the CLI's own default tier — measures the tool as shipped, not a tuned variant |
| `model_context_window` | `272000` | the published input-context size for the model family; must be explicit because custom providers get fallback metadata (probe finding) |
| `web_search` | disabled (`web_search = "disabled"`) | §8.1.1 — no uncontrolled retrieval inputs |
| MCP servers | none | §8.1.1 |
| Env allowlist | `PATH, LANG, LC_ALL, TERM, TMPDIR` (+ `OPENAI_API_KEY` as the single secret) | §8.1.1 sanitized environment |
| Cache policy | disabled; fresh `CODEX_HOME` per trial | §8.1.1 ephemerality |
| Sampling seed | none — **N=5 unseeded trials per cell** | the pinned build exposes no seed (probe finding; §6.5 fallback) |
| Timeout | 1800 s per run | §10 locked decision #5 (unchanged) |
| Ladder | 1x/2x/5x/10x/20x/50x + breakdown probe | §10 locked decision #6 (unchanged) |

## Registration procedure (pilot machine, once, before any run)

```bash
cd research/repo-bloat-benchmark
python3 -m harness.runner.register_env \
    --arm harness/runner/pilot_arm_codex.json --out registered_env.json
```

The fingerprint is **machine-bound by design** (it covers the allowlisted
env *values*): registration runs on the machine that will run the pilot,
after installing the pinned CLI. The emitted `registered_env_fingerprint`
goes into the experiment config next to `"freeze"`; every trial re-derives
it and aborts on mismatch (§8.1.1).

## Residual model-id risk (accepted, recorded)

`gpt-5.1-codex-max` availability on the billing account is confirmed by the
**first-real-run calibration** (`first_run_calibration.py`, one paid request
— the only intentionally-billed step before the pilot). If the account does
not serve it, the fallback is to re-freeze `model_id` (+ context window) —
explicitly a new registration — before any pilot cell runs.
