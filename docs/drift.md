# `pdd checkup drift` Regeneration Stability

`pdd checkup drift` checks whether a dev unit remains behaviorally stable across repeated regeneration from the same prompt.

## Usage

```bash
pdd checkup drift <devunit>
pdd checkup drift <devunit> --runs 3
pdd checkup drift <devunit> --model <model>
pdd checkup drift <devunit> --from-evidence .pdd/evidence/devunits/<devunit>.latest.json
pdd checkup drift <devunit> --json
```

## What It Checks

- Regenerates code for each run unless `--dry-run` is set.
- Compares public API and implementation hash across runs.
- Runs discovered local pytest tests for the generated module.
- Honors configured story/verify validation statuses from evidence manifests.
- Runs policy checks when policy/evidence is configured.

## Exit Semantics

- `0`: Stable (public API unchanged and all configured checks pass on all runs)
- `1`: Unstable (API drift or behavior/policy failure on any run)

## Notes

- `--dry-run` skips regeneration and evaluates current artifact stability only.
- `--from-evidence` resolves prompt/code from manifest data and output paths.
- Behavior drift is stricter than implementation drift: hash changes can be acceptable when behavior remains stable.
