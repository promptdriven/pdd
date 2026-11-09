# Contributing to PDD

Read the entire [Prompting guide](docs/prompting-guide.md) before authoring a Story or prompt in the actual conversation. Use the same guide as the skill and recipes; do not create a competing set of prompt rules.

## Work from a local checkout

For a checkout with less history to download, make a shallow clone:

```sh
git clone --depth 1 https://github.com/promptdriven/pdd.git
cd pdd
```

This checkout has limited history. If you need the full history, run `git fetch --unshallow` inside the checkout.

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

The bundled `pdd-small-change`, `pdd-bug` and `pdd-feature` workflow skills have size limits enforced by [SKILLS4 in the skill tests](test/skills.test.mjs). Their `SKILL.md` limits are 3,072 bytes for small-change and 4,096 bytes each for bug and feature. Declared step briefs are limited to 15 lines and 1,228 bytes each, except `prompt-story` (1,638 bytes), `review` (2,304) and `change` (1,536). Each `steps/autopilot.md` is an Autopilot overlay with its own 3,072-byte limit, separate from ordinary step limits. SKILLS4 does not apply these workflow limits to `pdd-product`.

Measure file bytes before editing and compare them with the applicable limits:

```sh
wc -c skills/pdd-{small-change,bug,feature}/SKILL.md skills/pdd-{small-change,bug,feature}/steps/*.md
```

Also count ordinary step lines as the test does: trim trailing whitespace, then split on newlines. A checkout snapshot measured the three `SKILL.md` files at 2,741, 4,091 and 4,088 bytes respectively, leaving 331, 5 and 8 bytes; remeasure for the current checkout. The test is the authoritative source for current limits.

Put step-specific detail in the appropriate existing step brief and shared applicable guidance in [RUNBOOK.md](RUNBOOK.md), keeping its [skill copy](skills/pdd-prompting/RUNBOOK.md) in sync. Do not duplicate rules already in `SKILL.md` or use `steps/autopilot.md` as general overflow. The checks require the exact declared step files plus the Autopilot overlay and exact top-level contents; adding another file there requires a separate change to the checks and packaging.

The CLI/package owner maintains the package allowlist. Documentation changes must preserve a complete skill bundle: canonical guide, skill entrypoint, references, recipes and example links must resolve from a clean extracted package. To inspect a package without installing globally:

```sh
mkdir -p /tmp/pdd-alpha-pack
npm pack --ignore-scripts --pack-destination /tmp/pdd-alpha-pack
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
production modules, either
in the entrypoint or through a shared fixture. It gives each test process a
private temporary HOME and PDD_INTERPRETER_QUEUE and clears inherited state and agent config directory
overrides. Explicit fixture homes still select their own default state paths.
It also clears inherited `PDD_SUITE_QUEUE`, `PDD_VM_SUITE_LOCK` and `SUITE`
before test code runs. Tests can then set their own fixture queue selectors.
The assigned `PDD_CHECK_CPUS` hint stays available.
Import the helper first when adding a test without a shared fixture. `npm test`
also preloads it. The owning process removes its temporary home on exit. OS account-home lookup
requires an injected `userInfo` fake; an un-injected lookup fails the process
with `PDD_TEST_ACCOUNT_HOME`, even if the caller catches the error.
The helper also blocks filesystem access to the default machine interpreter queue
with `PDD_TEST_INTERPRETER_QUEUE`, even when the error is caught. A test that
replaces its environment or starts a native pdd check must carry a private queue
selector. HOME and TMPDIR alone do not isolate the machine queue. Fresh fixture environments and narrowed repair-test environments must keep their own PDD_INTERPRETER_QUEUE selector.

The runtime workspace fixture uses `f.env.HOME` for its private home. It leaves
`<parent>/home` available for tests that need a separate consumer home.

Run a focused file with `node --test test/<file>.test.mjs`. To preload the same
isolation for a new test, use
`node --import ./test/helpers/test-home.mjs --test test/<file>.test.mjs`.
The home isolation regression uses synthetic caller folders and the existing
GitHub, Herdr and interpreter fakes. It needs no account or live service.
