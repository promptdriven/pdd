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
- Re-runs configured story and verify checks per candidate when evidence marks them as required.
- Runs policy checks when policy/evidence is configured.
- Stops regeneration when `--max-cost` is exceeded.

## Exit Semantics

- `0`: Stable (public API unchanged and all configured checks pass on all runs)
- `1`: Unstable (API drift or behavior/policy failure on any run)

## Notes

- `--dry-run` skips regeneration and evaluates current artifact stability only.
- `--from-evidence` resolves prompt/code from manifest data and output paths.
- Behavior drift is stricter than implementation drift: hash changes can be acceptable when behavior remains stable.
