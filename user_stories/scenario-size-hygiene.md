# Warn on oversized scenario files in offline lint

As a developer running offline `pdd lint` on Story scenarios, I want non-blocking size and call-budget warnings calibrated to configurable limits, so that genuinely oversized scenarios are split into companion files without false positives on normal 10–15 step suites.

## Acceptance criteria

1. Running `pdd lint` on a scenario with 16 steps prints a non-blocking `scenario-oversized` warning naming the file, `16 scenario steps (limit: 15)`, and companion-file splitting advice (`tests/<story>.<focus>.json`), and exits with code 0.
2. Running `pdd lint` on a scenario with 15 steps and 200 bytes of `initial_world` emits zero `scenario-oversized` warnings and exits with code 0.
3. Running `pdd lint` on an 8-step scenario whose `initial_world` and `seeds` total 20,000 serialized bytes emits a non-blocking `scenario-oversized` warning citing the byte count and `limit: 16384`, and exits with code 0.
4. Configuring `pdd.json` `"lint": { "scenario": { "max_steps": 10 } }` causes a 12-step scenario to emit a `scenario-oversized` warning citing `limit: 10`, while setting `"rules": { "scenario-oversized": "off" }` suppresses the warning.
5. Configuring `"lint": { "rules": { "scenario-oversized": "error" } }` reports an oversized scenario as an error and exits with code 1.

## Rules to check

- Default `scenario-oversized` findings are advisory warnings only. Forbidden: exiting with code 1 on an oversized scenario unless the repository configures `"scenario-oversized": "error"`.
- Scenarios at or below configured step, serialized state byte, and lower-bound call limits emit zero `scenario-oversized` warnings. Forbidden: false-positive warnings on 10–15 step scenarios under default limits.
- Invalid `"lint.scenario"` limits (zero, negative, or non-integer values) fail lint configuration validation. Forbidden: silently ignoring invalid numeric limits.

## Verification boundary

The prompt scenario verifies the pure scenario-hygiene evaluation rules over supplied scenario objects and limits. Native tests separately verify `pdd.json` config parsing, merge-base trust, `pdd lint` / `pdd lint --local` CLI exit codes, and scoped `--diff` runs.
