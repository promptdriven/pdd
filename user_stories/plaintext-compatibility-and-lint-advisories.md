# See concise compatibility and advisory headings in plain-text lint and test

As a developer running pdd lint and pdd test in a terminal, I want plain-text output to summarize compatibility on one line and label non-blocking lint warnings as advisories, so that multi-step runs stay readable and advisories do not look like blocking failures.

## Acceptance criteria

1. Plain-text compatibility output for a supported 3-step scenario prints one "Compatibility (tests/place-order.json): supported (association matched); 3 steps (3 operations, 0 edges); execution ordinary; resources simulated; complete true; engine 088d558b9373." summary line followed by "  Client advice (application author): Behavioral execution remains required. Installed-engine, host/profile and physical-observation proof remains unproved.", with no multiline JSON.
2. Plain-text compatibility output for an unassociated or unsupported report names the client issue and non-supported reason code on that single "Compatibility (...)" line (such as "issue capability-association-mismatch; non-supported: binding-missing"), while detailed compatibility output prints the full pretty-printed compatibility JSON and compact client advice JSON.
3. A non-blocking warning from the PDD interpreter (such as "needs-hash-tool" on "prompts/place_order.prompt.md") prints under "Lint advisories (from the PDD interpreter):" with no "Lint problems" heading.
4. Blocking lint findings print under "Lint problems (from the PDD interpreter):" (or "Local lint problems:" in local mode) ahead of any "Lint advisories (from the PDD interpreter):" (or "Local lint advisories:") section when blocking findings and warnings appear together.

```pdd-boundary
prompts/cli/lint-compatibility-display.prompt.md
```

## What must not change

- `pdd lint --json`, `pdd test --json` and saved `summary.json` keep the full `compatibility`, `client_advice` and `problems` payloads unchanged.
- `pdd test --details` still prints the full pretty-printed compatibility JSON and compact client advice JSON alongside detailed check lines.
- Non-blocking lint advisories keep exit code 0 when selected tests pass, while blocking lint findings still refuse admission with exit code 4.

## Rules to check

- Default plain-text compatibility display emits exactly one `Compatibility (...)` line (plus one indented `Client advice (...)` line when client advice is present) and never spans multiple JSON lines. Forbidden: a newline inside the `Compatibility (...)` summary line or multiline JSON braces when detailed mode is off.
- Warning findings appear only under an advisories heading, and blocking findings appear only under a problems heading ahead of advisories, preserving relative input order within each group. Forbidden: a warning under `Lint problems` or `Local lint problems`, a blocking finding under `Lint advisories` or `Local lint advisories`, or advisories printed before blocking problems.
- Compatibility and lint diagnostic formatting is pure and read-only. Forbidden: mutating any supplied `compatibility`, `clientAdvice` or `problems` input.

## Verification boundary

The prompt scenario checks the pure display contract with synthetic compatibility
reports and lint diagnostics. Native CLI tests separately cover `pdd lint`,
`pdd test`, `pdd test --details`, `--json`, Try stderr on not-run lint and saved
`--read` output; those CLI transport and persistence paths are not claimed as
prompt-interpreter evidence.
