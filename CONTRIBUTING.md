# Contributing to PDD

Read the entire [Prompting guide](docs/prompting-guide.md) before authoring a Story or prompt in the actual conversation. Use the same guide as the skill and recipes; do not create a competing set of prompt rules.

## Work from a local checkout

Use Node.js 22.16.0 or newer. The CLI and tests have no dependency installation step:

```sh
node bin/pdd.mjs --help
node --test test/cli.test.mjs
npm test
```

PDD is developed on the `alpha` branch of [promptdriven/pdd](https://github.com/promptdriven/pdd/tree/alpha). Open pull requests against `alpha`, not `main`. Use a topic branch. Change a module's prompt before changing its behavior. Explain the useful outcome in a Story and author expected cases from that contract rather than copying the implementation's answer. Keep prompts, tests and code within the same reviewed change. Choose a [workflow or recipe](docs/workflows.md) when helpful.

The offline native-launch and Herdr transport tests exercise responses larger than 64 KiB, including nonzero exits. Simulated child programs set `process.exitCode` and let buffered stdout/stderr drain before exit. The parent reads complete replies before parsing JSON; keep the full arguments, full-access flags and exit-status assertions. These tests make no model calls.

## Review

Show what changed after feedback, including any unresolved point. A proposed contract requires the person's actual decision before treating it as accepted. Report drafted expectations, executed tests and manual observations separately. A passing example is not proof about other projects; ordinary tests are not formal verification.

Prepare a PR with the reason for the change, the behavior affected, actual test commands/results and remaining limits. Publish or merge only through the authorized repository workflow. Review and a green public full suite are required before publication of public source. Keep operational reports, private logs and credentials outside the tree.

## Package checks

The CLI/package owner maintains the package allowlist. Documentation changes must preserve a complete skill bundle: canonical guide, skill entrypoint, references, recipes and example links must resolve from a clean extracted package. To inspect a package without installing globally:

```sh
mkdir -p /tmp/pdd-alpha-pack
npm pack --ignore-scripts --pack-destination /tmp/pdd-alpha-pack
```

Use a fresh temporary directory if that destination already contains prior artifacts. Extract the returned archive into another clean directory, run its local CLI and inspect its files. Do not publish to npm or change a global `pdd` to test packaging.

## Scope and license

Contributions are under the repository's [MIT license](LICENSE). Retain applicable notices. Keep the package self-contained, with no hosted services, private dependencies, operational fixtures or credentials in source or package artifacts. An optional proposal for a future capability is not an implemented public command.

## Native tests during Autopilot work

Run `node scripts/affected-tests.mjs --base BASE` to inspect the affected-test
plan. Use the run's base commit. Add `--run --report /external/run/working-tests.json`
to execute it and retain results outside the checkout. The plan includes changed
tests, reverse module consumers, prompt scenarios and replay consumers, and the
fixed CLI version and command catalog smoke tests. Computed file or process
access selects conservative consumers. Shared helpers, package files, runner
changes and unavailable inventories select the full suite. Full fallbacks use
`scripts/vm-suite-lock.sh`, the shared suite queue adapter. Do not omit a selected
test to make a run pass.

The selector retains all plausible extensionless file and index targets. It uses
full fallback for reachable directory package entry points and unclassified slash
syntax, including regex and division expressions. These fallbacks protect test
coverage when the scanner cannot determine the loaded dependencies.
Loader aliases and unclassified Unicode escapes in executable identifiers select
their consumers and all reverse consumers conservatively.

Record the working files, command, mode, fallback cause, counts and `suiteMinutes`
in the PR. Keep these results separate from the merge result. The merge owner
runs the full suite once through the shared queue on the exact clean PR head,
reuses an existing green result on that head, and reports the head and result in
the PR. A new head requires a new result. Missing, stale or failed full results
block merge. An affected pass is not the full-suite gate.

When the cost ledger from #3061 is installed, record each measured execution
once with `pdd workflow cost ISSUE --input -`: use a unique measurement `id` and
the report's non-null `suiteMinutes`. For queued full runs, use the queue's
execution-only measurement; the adapter leaves `suiteMinutes` null because its
wall time includes queue wait. Include working executions and the final full suite.
Compare suite minutes per merged issue with the same work scope. Do not count
selection time, queue wait or a file-count estimate as executed suite minutes.
