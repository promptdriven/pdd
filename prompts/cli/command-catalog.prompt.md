# Local command catalog

Own `src/command-catalog.mjs`; export `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, `REMOVED_COMMANDS`, `NAMES` ([Names](#names)), `PUBLIC_HELP_TEXT` ([Help text](#help-text)), and `BUNDLED_WORKFLOW_NAMES` (`feature`, `bug`, `small-change`, `product`).

Each route has a stable `id`, exact `prefix`, `local` disposition, operand/option specs, and plain help forms. Expose no excluded command, private schema/type, service flag, or removed `pdd workflow` / `pdd dependencies` route. Help, parser, and shell completion share this one authority.

## Authoring

Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories. Follow the [public boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy.

## Names

`NAMES` is the one place for the words of core commands: `{test: 'test', lint: 'lint', simulate: 'simulate', run: 'run', requestUptake: 'ack'}`. Help forms and completion derive `test`, `lint`, and `simulate` from `NAMES`.

| Route id | Prefix | Local | Quiet words | Removed words |
|---|---|---|---|---|
| `check` | `test` | `runtime-check` | | `check` (new command `pdd test`) |
| `lint` | `lint` | `lint` | | `check` with `--lint` (new command `pdd lint`) |
| `try` | `simulate` | `runtime-try` | `sim` | `try` (new command `pdd simulate`) |

- A quiet word (`sim`, `-V`) parses like the prefix of its route, with nothing added. Completion never offers it. Help names `sim` once, in the description of the first `simulate` form.
- A removed word runs nothing. The [argument parser](argument-parser.prompt.md#removed-names) refuses route-owned removed words (`check`, `check --lint`, `try`) and standalone `REMOVED_COMMANDS` (`workflow` → actionable pointer to `/pdd`, `pdd prove`, and `pdd autopilot`) with exit 2 and zero side effects.

## Core PDD workflow routes

- `setup` (`setup`, local `setup`): optional flag `--yes` and text `--skills-dir`. Form: `pdd setup [--yes] [--skills-dir PATH]`.
- `init` (`init`, local `init`): no operands or options. Form: `pdd init`.
- `status` (`status`, local `status`): optional repeated text `path`, flags `--changed` and `--json`. Form: `pdd status [PATH...] [--changed] [--json]`.
- `check` (`test`, local `runtime-check`): optional repeated text `story`, options `--target` (`code`), `--affected`, `--journeys`, `--lf`, `--cache-clear`, `--fresh`, `--json`, `--details`, `--timeout` (`1..120`), `--max-calls` (`1..1000`), `--max-total-calls` (`1..999999`), `--no-restart-replacement`, `--read`, `--retry`, `--reconcile` (`uuid`), `--explain-bindings`, `--files`, `--app-map`, `--screen`, `--drawing`, `--look`, and hidden options `--lint`, `--local`, `--remote`, `--diff`, `--base`, `--codex`, `--issue`, `--emit-v1`, `--write`, `--bind-criteria`, `--request`.
  - Forms include `pdd test --target code [STORY...] [--json]`, `pdd test --affected [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]`, `pdd test --journeys [JOURNEY] [--max-calls N]`, `pdd test [PATH|STORY...] [--lf] [--cache-clear] [--fresh] [--json] [--details] [--timeout MIN] [--max-calls N]`, `pdd test [PATH|STORY...] [--max-total-calls N] [--no-restart-replacement] [--max-calls N] [--timeout MIN] [--json]`, `pdd test --read [BATCH|CALL_ID] [--json] [--details] [--timeout MIN]`, `pdd test --retry BATCH [--json] [--details] [--timeout MIN]`, `pdd test --reconcile REQUEST_ID [--json]`, `pdd test --explain-bindings [STORY...] [--json]`, `pdd test --files [STORY...] [--app-map PATH] [--json]`, and `pdd test --screen URL --drawing PATH [--look] [--json]`.
- `lint` (`lint`, local `lint`, implies `--lint`): optional repeated text `story`, options `--json`, `--local`, `--remote`, `--diff` (`optional-text`), `--base`, `--timeout` (`1..120`), `--max-calls` (`1..1000`), `--codex`, `--issue`, `--emit-v1`, `--write`, `--bind-criteria`. Offline-first by default (`0` AI, `0` network, `0` batch-state writes); `--remote` runs hosted interpreter lint.
- `prove` (`prove`, local `prove`): no operands, options `--base`, `--test`, `--expect`, `--overlay`, `--setup`, `--timeout` (`1..120`), `--json`. Forms cover zero-flag merge-base proof (`pdd prove [--base REF] [--timeout MIN] [--json]`) and isolated base-vs-head bug-contrast proof (`pdd prove --base REF --test CMD --expect TEXT [--overlay GLOB] [--setup CMD] [--timeout MIN] [--json]`).
- `try` (`simulate`, quiet `sim`, local `runtime-try`): optional text `story`, options `--product`, `--parts`, `--journey`, `--agent`, `--tab` (`call|screen|terminal|world`), `--new`, `--fresh`, `--page`, `--cli`, `--shell`, `--save-last`, `--serve` (`optional-integer` `1..65535`, default `8080`), `--max-calls` (`1..1000`), `--no-open`, `--stop`, `--app-map`, `--no-wait`.
- `approve` (`approve`, local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)): required text `prompt`, optional text `--said`. Form `pdd approve PROMPT [--said WORDS]` includes the shared quoted-heredoc approval template.
- `files` (`files`, local `project-files`, [files view](files.prompt.md)): flag `--json`. Form `pdd files [--json]`.
- `owner` (`owner`, local `file-owner`, [file owner lookup](file-owner.prompt.md)): required repeated text `path`, flag `--json`. Form `pdd owner PATH... [--json]`.
- `update` (`update`, local `update-sync`, [Changed-map wrapper](update-sync.prompt.md)): optional repeated text `file`, options `--from` (text), `--branch` (flag), `--all` (flag), `--check` (flag), hidden `--write` (flag, refused read-only by handler without advertising in help or completion), and `--json` (flag). Form: `pdd update [FILE...] [--from RANGE] [--branch] [--all] [--check] [--json]`.
- `contracts` (`contracts`, local `contracts`) and `contracts.sync` (`contracts sync`, local `contracts-sync`, flag `--write`).
- `jobs` (`jobs`, local `runtime-jobs`): no operands or options. Form `pdd jobs`.
- `mcp` (`mcp`, local `mcp`): no operands or options. Form `pdd mcp`.
- `upgrade` (`upgrade`, local `upgrade`): flag `--main`. Form `pdd upgrade [--main]`.

## Cloud accounts routes

Catalog local disposition `accounts` ([Cloud accounts CLI](accounts-cli.prompt.md)): `accounts`, `accounts.list`, `accounts.status`, `accounts.add`, `accounts.import`, `accounts.use`, `accounts.next`, `accounts.codex` (`passthrough: true`), `accounts.sync` (hidden `--print-codex-home`), `accounts.auto`, `accounts.pause`, `accounts.unpause`, `accounts.share`, `accounts.accept`, `accounts.unshare`, `accounts.leave`, `accounts.remove`, and `accounts.log`.

## Product and graph routes

- `product.status` (`product status`, local `product-status`, `--json`, `--through prompt-pr|code`)
- `product.next` (`product next`, local `product-next`, `--through prompt-pr|code`)
- `product.start` (`product start`, local `product-start`, operand `run`, `--no-run`, `--agent` text with `codex|claude|gemini|agy` choices, `--through prompt-pr|code`, `--base`): form `pdd product start RUN [--no-run] [--agent codex|claude|gemini|agy|ENTRY] [--through prompt-pr|code] [--base BRANCH]` describes creating or reusing the scoped run issue and printing a `/pdd` handoff prompt (`--no-run` only prepares the issue; no interpreter calls). [Product](product.prompt.md) owns behavior.
- `product.contracts` (`product contracts`, local `contracts`)
- `graph` (`graph`, local `issue-dependency-graph`, `--open`, `--issue`, `--repo`)

## Autopilot routes

Catalog `autopilot.doctor`, `autopilot.start` (with `--runs`, `--checks`, `--engine`, `--label`, `--issues`, `--issue`, `--mode`, `--report`, `--decisions`, `--intake`, `--share`, `--agent`, hidden `--pool`, `--auto-update`), `autopilot.suite` (`--command`, `--timeout` `0..120`), `autopilot.status` (`--all`, `--json`), `autopilot.logs` (`issue`, `--issue`, `--follow`, `-f`, `--lines` `1..5000`, `--json`), `autopilot.stop`, `autopilot.observe`, `autopilot.auto`, `autopilot.off`, `autopilot.trust`, `autopilot.untrust`, `autopilot.add`, `autopilot.release`, `autopilot.intake`, `autopilot.graph`, `autopilot.report`, `autopilot.regressions`, `autopilot.alerts`, `autopilot.alert`, and `autopilot.check-base`. [Autopilot launcher](autopilot-launcher.prompt.md) and [Autopilot alerts](autopilot-alerts.prompt.md) own execution.

## Regression scan

Register `autopilot.regressions`, prefix `autopilot regressions`, local `autopilot-regressions`, no operands, Boolean `--json` and text `--file`. Form: `pdd autopilot regressions [--json] [--file PATH]`. Description: Read core merge history and GitHub regression evidence; optionally save a local report, without GitHub writes or reverts.

## Metrics, shell, help, and version routes

- `metrics`, `metrics.stages`, `metrics.skills`, `metrics.full`, `metrics.on`, `metrics.off`
- `completion` (`completion bash|zsh`)
- `help` (`pdd`, `pdd --help`, `pdd -h`, `pdd help`, `pdd help prompting`, topic `prompting`)
- `version` (`--version`, quiet `-V`) and `version.detailed` (`-VV`)

## Help text

Export the frozen `PUBLIC_HELP_TEXT` object with `heading`, `usageLine`, `quickStartLines`, `groups`, `focusedHelpLines`, `closingLines`, `learnLines`, and `promptingLines`. Keep every rendered line of root help within 80 columns. Groups order human-first: `Core PDD workflow`, `Cloud accounts (pdd accounts --help)`, `Product & dependency graph (pdd product --help)`, `Autopilot (pdd autopilot --help)`, and `Metrics, shell & help (pdd metrics --help)`.

## Learn PDD

The catalog owns the Learn PDD and `pdd help prompting` templates; the CLI substitutes `PACKAGE_ROOT` without reading files.

```text
In PDD, prompts are the source. Code follows the prompts.
1. Prompt: prompts/NAME.prompt.md. Write what the program does in plain English, then ## Dependencies.
2. Story: user_stories/STORY.md. Write one thing that a person can do, then a numbered ## Acceptance criteria list.
3. Test: tests/STORY.json. When the repo keeps its own tests in tests/ or test/, use tests/runtime/ or test/runtime/. Write compact JSON steps with an exact check for each criterion.
4. Check: run pdd test --files STORY && pdd test STORY in one shell call. Test includes interpreter lint (0 AI calls); use pdd lint for lint-only diagnosis.
5. Approve: a person reads each prompt and runs pdd approve PROMPT. New behavior needs a person.
```

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- [Argument parser](argument-parser.prompt.md) and [Runtime seam](runtime-seam.prompt.md) consume the catalog contract.
