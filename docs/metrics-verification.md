# Verify local metrics capture

Use Node 22.16 or newer and a fresh checkout. No installation or model service is needed for the repository's native tests. Run these commands from the checkout:

```sh
node --version
node --test test/metrics*.test.mjs
node --test test/autopilot-review-wake.vectors.test.mjs test/autopilot-wake.formal.test.mjs test/workflow-concurrent-progress.*.test.mjs
```

The tests create disposable Git repositories and controlled GitHub, Herdr and native session metadata fixtures. They exercise the real CLI process for report, export/import, metadata parsing and retained journal recovery after process exit. Native workflow library consumers exercise selector decisions, launch delivery outcomes, exact session matching and terminal code publication. Fixtures supply external observations; they do not establish a real worker start, hosted checker verdict or live publication.

`metrics-composition.integration.test.mjs` additionally checks that failed capture, gap writes, rejected drains and throwing warnings preserve the native workflow outcome. It preserves time-only wakes, forwards metadata with draft/base/adoption options, rejects native status rename failures normally, and exports cancelled and completed runs beyond the 200-entry selection index. Existing lifecycle and readiness replays cover absent/mismatched native identity and stale/current PR heads. Expected results come from the metrics Story and the owning native contracts.

For an installed report demonstration in a disposable Git repository with an origin remote, invoke the explicit candidate executable:

```sh
/absolute/candidate/bin/pdd.mjs metrics --help
/absolute/candidate/bin/pdd.mjs metrics --json
/absolute/candidate/bin/pdd.mjs metrics export /absolute/proof/first.json
/absolute/candidate/bin/pdd.mjs metrics import /absolute/proof/first.json
/absolute/candidate/bin/pdd.mjs metrics import /absolute/proof/first.json
/absolute/candidate/bin/pdd.mjs metrics --json --expected-source absent-proof-source
```

Compare retained source/event identities before and after import; a missing source is incomplete coverage. Cohort and queue activity are null outside an explicit date scope. Use `metrics --date YYYY-MM-DD --timezone UTC --json` for daily activity. Manual `metrics record` data must be labeled manual and kept separate from automatic capture proof. No approval or workflow progression is required for report commands.

Keep command argv, UTC start/end, stdout/stderr, exits, revision and fixture identities outside the checkout. Remove only the disposable repositories and exported files after retaining the evidence. Independent verification repeats the commands from a fresh checkout or the exact offline archive. Setup success and fixture-based native execution remain separate from live integration acceptance.
