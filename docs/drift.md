# `pdd checkup drift` Regeneration Stability

`pdd checkup drift` checks whether a dev unit remains behaviorally stable across repeated regeneration from the same prompt.

## Usage

```bash
pdd checkup drift <devunit>
pdd checkup drift <devunit> --runs 3
pdd checkup drift <devunit> --model <model>
pdd checkup drift <devunit> --from-evidence .pdd/evidence/devunits/<devunit>.latest.json
pdd checkup drift <devunit> --json
pdd checkup drift <devunit> --max-cost 5.0
```

## What It Checks

- Regenerates each trial into an isolated temp path (does not overwrite the worktree code file).
- Compares each candidate's public API and hash against the pre-run baseline artifact.
- Runs discovered local pytest tests against sandboxed candidate copies.
- Re-runs configured story and verify checks when evidence marks them as required.
- Runs policy checks when policy/evidence is configured (requires `pdd checkup gate` in the installed package).
- Applies a default `--max-cost` budget for non-dry-run regeneration (override with `--max-cost`).

## Behavioral Check Scope (important)

| Check | What it evaluates |
|-------|-------------------|
| **Tests** | Sandbox overlay copies source roots (`pdd/`, full `src/`, import-discovered top-level packages), swaps in the candidate module, copies tests/`conftest.py`/helpers, and runs pytest with overlay `PYTHONPATH` |
| **Stories** | Prompt↔story consistency for the dev unit prompt (live `detect --stories` scope); not a direct re-validation of regenerated code semantics |
| **Verify** | Candidate code against its verification program (live `pdd verify` on temp copies) |
| **Policy** | `pdd checkup gate` when a policy file exists or evidence explicitly records a policy/gate validation key; **fails closed** only in that case if gate is not installed (ordinary evidence alone does not enable policy) |

## Cost Controls

- Non-dry-run drift checks use a default max budget (`DEFAULT_MAX_COST_USD`, currently $20).
- Pass `--max-cost` to tighten or raise the cap.
- `--dry-run` skips regeneration and does not apply the regeneration budget default.

## Exit Semantics

- `0`: Stable (public API unchanged vs baseline and all configured checks pass on all completed runs)
- `1`: Unstable (API drift, behavioral failure, budget exceeded, or policy unavailable when configured)

## Notes

- `--dry-run` skips regeneration and evaluates the current baseline artifact only.
- `--from-evidence` resolves prompt/code from manifest data and output paths.
- Behavior drift is stricter than implementation drift: hash changes can be acceptable when behavior remains stable.
- This command is distinct from `pdd/ci_drift_heal` (CI prompt/example auto-heal) and `pdd contracts drift` (contract/code conformance).
