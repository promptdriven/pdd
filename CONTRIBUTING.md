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

## Test homes

Tests that use default home paths load `test/helpers/test-home.mjs` before
production modules, either
in the entrypoint or through a shared fixture. It gives each test process a
private temporary HOME and clears inherited state and agent config directory
overrides. Explicit fixture homes still select their own default state paths.
Import the helper first when adding a test without a shared fixture. `npm test`
also preloads it. The owning process removes its temporary home on exit. OS account-home lookup
requires an injected `userInfo` fake; an un-injected lookup fails the process
with `PDD_TEST_ACCOUNT_HOME`, even if the caller catches the error.

The runtime workspace fixture uses `f.env.HOME` for its private home. It leaves
`<parent>/home` available for tests that need a separate consumer home.

Run a focused file with `node --test test/<file>.test.mjs`. To preload the same
isolation for a new test, use
`node --import ./test/helpers/test-home.mjs --test test/<file>.test.mjs`.
The home isolation regression uses synthetic caller folders and the existing
GitHub, Herdr and interpreter fakes. It needs no account or live service.
