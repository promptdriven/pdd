# Contributing to PDD

Read the entire [Prompting guide](skills/pdd/references/prompting.md) before authoring a Story or prompt in the actual conversation. Use the same guide as the skill and recipes; do not create a competing set of prompt rules.

## Work from a local checkout

For a checkout with less history to download, make a shallow clone:

```sh
git clone --depth 1 https://github.com/promptdriven/pdd.git
cd pdd
```

This checkout has limited history. If you need the full history, run `git fetch --unshallow` inside the checkout.

Use Node.js 22.16.0 or newer and install dependencies with `npm ci --ignore-scripts`:

```sh
npm ci --ignore-scripts
node bin/pdd.mjs --help
node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test test/cli.test.mjs
npm test
```

PDD is developed on the `main` branch of [promptdriven/pdd](https://github.com/promptdriven/pdd). Open pull requests against `main` from a topic branch. Change a module's prompt before changing its behavior. Explain the useful outcome in a Story and author expected cases from that contract rather than copying the implementation's answer. Keep prompts, tests and code within the same reviewed change. Choose a [workflow or recipe](docs/workflows.md) when helpful.

The offline native-launch and subprocess transport tests exercise responses larger than 64 KiB, including nonzero exits. Simulated child programs set `process.exitCode` and let buffered stdout/stderr drain before exit. The parent reads complete replies before parsing JSON; keep the full arguments, full-access flags and exit-status assertions. These tests make no model calls.

## Review

Show what changed after feedback, including any unresolved point. A proposed contract requires the person's actual decision before treating it as accepted. Report drafted expectations, executed tests and manual observations separately. A passing example is not proof about other projects; ordinary tests are not formal verification.

Prepare a PR with the reason for the change, the behavior affected, actual test commands/results and remaining limits. Publish or merge only through the authorized repository workflow. Review and a green public full suite are required before publication of public source. Keep operational reports, private logs and credentials outside the tree.

## Package checks

Keep skill files concise and run `npm test` (including `test/skills.test.mjs` and `test/cli.test.mjs`) to verify skill frontmatter, canonical guide parity, and packed package contents. The test suite is the authoritative source for current skill structure and packaging rules.

Documentation and packaging changes must preserve a complete skill bundle so canonical guides, skill entrypoints, references, recipes and example links resolve from a clean extracted package. To inspect a package without installing globally:

```sh
mkdir -p /tmp/pdd-pack-check
npm pack --ignore-scripts --pack-destination /tmp/pdd-pack-check
```

Use a fresh temporary directory if that destination already contains prior artifacts. Extract the returned archive into another clean directory, run its local CLI and inspect its files. Do not publish to npm or change a global `pdd` to test packaging.

## Autopilot factory

Run `scripts/factory-test.sh` for the complete offline Autopilot factory. It uses
real Git and native PDD workflows with disposable service fakes and scripted
agents. See [the factory test](docs/autopilot-factory.md) for its scenarios,
isolation and limits. A candidate gap remains a failing test; retain its expected
outcome and report the gap. This command does not run the public full suite.

## Scope and license

Contributions are under the repository's [MIT license](LICENSE). Retain applicable notices. Keep the package self-contained, with no hosted services, private dependencies, operational fixtures or credentials in source or package artifacts. An optional proposal for a future capability is not an implemented public command.

## Test homes

Tests that use default home paths load `test/helpers/test-home.mjs` before
production modules, either in the entrypoint or through a shared fixture. It
gives each test process a private temporary HOME and clears inherited state and
agent config directory overrides. Explicit fixture homes still select their own
default state paths. It also clears inherited `PDD_SUITE_QUEUE`,
`PDD_VM_SUITE_LOCK` and `SUITE` before test code runs so tests can set their own
fixture queue selectors. The assigned `PDD_CHECK_CPUS` hint stays available.
Import the helper first when adding a test without a shared fixture. `npm test`
also preloads it alongside `test/helpers/test-net-guard.mjs`. The owning process
removes its temporary home on exit. OS account-home lookup requires an injected
`userInfo` fake; an un-injected lookup fails the process with
`PDD_TEST_ACCOUNT_HOME`, even if the caller catches the error.

The runtime workspace fixture uses `f.env.HOME` for its private home. It leaves
`<parent>/home` available for tests that need a separate consumer home.

Run a focused file with
`node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test test/<file>.test.mjs`.
The home isolation regression uses synthetic caller folders and the existing
GitHub and interpreter fakes. It needs no account or live service.

For repository structural maintenance, see the contributor [refactor runbook](docs/refactor-runbook.md).
