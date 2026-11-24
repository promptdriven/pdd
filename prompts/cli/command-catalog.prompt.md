# Local command catalog

Own `src/command-catalog.mjs`; export `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, `REMOVED_COMMANDS`, `NAMES` ([Names](#names)), `PUBLIC_HELP_TEXT` ([Help text](#help-text)), and `BUNDLED_WORKFLOW_NAMES` (`feature`, `bug`, `small-change`, `product`).

Each route has a stable `id`, exact `prefix`, `local` disposition, operand/option specs, and plain help forms. Expose no excluded command, private schema/type, service flag, or removed `pdd workflow` / `pdd approve` / `pdd dependencies` route. Help, parser, and shell completion share this one authority.

## Authoring

Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories. Follow the [public boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy.

## Names

`NAMES` is the one place for the words of core commands: `{test: 'test', lint: 'lint', run: 'run'}`. Help forms and completion derive `test` and `lint` from `NAMES`, and `runJobs` derives the Try job label from `NAMES.run`.

| Route id | Prefix | Local | Quiet words | Removed words |
|---|---|---|---|---|
| `check` | `test` | `runtime-check` | | `check` (new command `pdd test`) |
| `lint` | `lint` | `lint` | | `check` with `--lint` (new command `pdd lint`) |
| `try` | *(empty — direct execution)* | `runtime-try` | | `simulate`, `sim`, `try` (in `REMOVED_COMMANDS`: `Run pdd <PROMPT.md|STORY> instead.`) |

- A quiet word (`-V`) parses like the prefix of its route, with nothing added. Completion never offers it.
- A removed word runs nothing. The [argument parser](argument-parser.prompt.md#removed-names) refuses route-owned removed words (`check`, `check --lint`) and standalone `REMOVED_COMMANDS` (`simulate`, `sim`, `try` → `Run pdd <PROMPT.md|STORY> instead.`, `workflow` → actionable pointer to `/pdd`, `pdd prove`, and `pdd autopilot`, and `approve` → actionable pointer to review and approve prompt changes in chat or GitHub PR review) with exit 2 and zero side effects.

## Core PDD workflow routes

- `setup` (`setup`, local `setup`): optional flags `--yes` and `--upgrade`, and text `--skills-dir`. Form: `pdd setup [--yes] [--skills-dir PATH] [--upgrade]`.
- `init` (`init`, local `init`): no operands or options. Form: `pdd init`.
- `status` (`status`, local `status`): optional repeated text `path`, flags `--changed` and `--json`. Form: `pdd status [PATH...] [--changed] [--json]`.
- `check` (`test`, local `runtime-check`): optional repeated text `story`, options `--target` (`code`), `--affected`, `--journeys`, `--lf`, `--cache-clear`, `--fresh`, `--json`, `--details`, `--timeout` (`1..120`), `--batch-timeout` (`1..1440`), `--max-calls` (`1..1000`), `--max-total-calls` (`1..999999`), `--no-restart-replacement`, `--read`, `--retry`, `--reconcile` (`uuid-or-batch`), `--reconcile-stale`, `--explain-bindings`, `--files`, `--app-map`, `--screen`, `--drawing`, `--look`, and hidden options `--lint`, `--local`, `--remote`, `--diff`, `--base`, `--codex`, `--issue`, `--emit-v1`, `--write`, `--bind-criteria`, `--request`.
  - Forms include `pdd test --target code [STORY...] [--json]`, `pdd test --affected [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]`, `pdd test --journeys [JOURNEY] [--max-calls N]`, `pdd test [PATH|STORY...] [--lf] [--cache-clear] [--fresh] [--json] [--details] [--timeout MIN] [--batch-timeout MIN] [--max-calls N]`, `pdd test [PATH|STORY...] [--max-total-calls N] [--no-restart-replacement] [--max-calls N] [--timeout MIN] [--json]`, `pdd test --read [BATCH|CALL_ID] [--json] [--details] [--timeout MIN]`, `pdd test --retry BATCH [--json] [--details] [--timeout MIN]`, `pdd test --reconcile REQUEST_ID|BATCH [--json]`, `pdd test --reconcile-stale [--json]`, `pdd test --explain-bindings [STORY...] [--json]`, `pdd test --files [STORY...] [--app-map PATH] [--json]`, and `pdd test --screen URL --drawing PATH [--look] [--json]`.
- `lint` (`lint`, local `lint`, implies `--lint`): optional repeated text `story`, options `--json`, `--local`, `--remote`, `--diff` (`optional-text`), `--base`, `--timeout` (`1..120`), `--max-calls` (`1..1000`), `--codex`, `--issue`, `--emit-v1`, `--write`, `--bind-criteria`. Offline-first by default (`0` AI, `0` network, `0` batch-state writes); `--remote` runs hosted interpreter lint.
- `prove` (`prove`, local `prove`): no operands, options `--base`, `--test`, `--expect`, `--overlay`, `--setup`, `--timeout` (`1..120`), `--json`. Forms cover zero-flag merge-base proof (`pdd prove [--base REF] [--timeout MIN] [--json]`) and isolated base-vs-head bug-contrast proof (`pdd prove --base REF --test CMD --expect TEXT [--overlay GLOB] [--setup CMD] [--timeout MIN] [--json]`).
- `try` (empty prefix — direct Prompt Interpreter execution, local `runtime-try`): optional text `target` (`.prompt.md` / `app-map.json` with optional verbatim program args, a Story selector, or `.` for whole-project mode), options `--product`, `--parts`, `--journey`, `--agent`, `--tab` (`call|screen|terminal|world`), `--new`, `--fresh`, `--page`, `--cli`, `--shell`, `--save-last`, `--serve` (`optional-integer` `1..65535`, default `8080`), `--max-calls` (`1..1000`), `--no-open`, `--stop`, `--app-map`, `--no-wait`, `--data`, `--show-data`, `--quiet`, `-q`. Forms cover direct execution (`pdd [OPTIONS] <PROMPT.md|STORY|.> [ARGS...]`), explicit `--page`, `--cli [--shell]`, `--serve [PORT]`, `--product`, `--save-last [STORY]`, and `--stop [STORY|PROMPT.md]`.
- `files` (`files`, local `project-files`, [files view](files.prompt.md)): flag `--json`. Form `pdd files [--json]`.
- `owner` (`owner`, local `file-owner`, [file owner lookup](file-owner.prompt.md)): required repeated text `path`, flag `--json`. Form `pdd owner PATH... [--json]`.
- `update` (`update`, local `update-sync`, [Changed-map wrapper](update-sync.prompt.md)): optional repeated text `file`, options `--from` (text), `--branch` (flag), `--all` (flag), `--check` (flag), hidden `--write` (flag, refused read-only by handler without advertising in help or completion), and `--json` (flag). Form: `pdd update [FILE...] [--from RANGE] [--branch] [--all] [--check] [--json]`.
- `contracts` (`contracts`, local `contracts`) and `contracts.sync` (`contracts sync`, local `contracts-sync`, flag `--write`).
- `jobs` (`jobs`, local `runtime-jobs`): no operands or options. Form `pdd jobs`.
- `mcp` (`mcp`, local `mcp`): no operands or options. Form `pdd mcp`.
- `upgrade` (`upgrade`, local `upgrade`): flag `--main`. Form `pdd upgrade [--main]`.
- `doctor` (`doctor`, local `doctor`): flag `--json`. Form `pdd doctor [--json]`. Read-only host health check for Node, competing `pdd` installs, login-shell `PATH` parity, agent skills, MCP configs, and `gh` sign-in.

## Cloud accounts routes

Catalog local disposition `accounts` ([Cloud accounts CLI](accounts-cli.prompt.md)): `accounts`, `accounts.list`, `accounts.status`, `accounts.add`, `accounts.import`, `accounts.use`, `accounts.next`, `accounts.codex` (`passthrough: true`), `accounts.sync` (hidden `--print-codex-home`), `accounts.auto`, `accounts.pause`, `accounts.unpause`, `accounts.share`, `accounts.accept`, `accounts.unshare`, `accounts.leave`, `accounts.remove`, and `accounts.log`.

## Product and graph routes

- `product.status` (`product status`, local `product-status`, `--json`, `--through prompt-pr|code`)
- `product.next` (`product next`, local `product-next`, `--through prompt-pr|code`)
- `product.start` (`product start`, local `product-start`, operand `run`, `--no-run`, `--agent` text with `codex|claude|gemini|agy` choices, `--through prompt-pr|code`, `--base`): form `pdd product start RUN [--no-run] [--agent codex|claude|gemini|agy|ENTRY] [--through prompt-pr|code] [--base BRANCH]` describes creating or reusing the scoped run issue and printing a `/pdd` handoff prompt (`--no-run` only prepares the issue; no interpreter calls). [Product](product.prompt.md) owns behavior.
- `product.contracts` (`product contracts`, local `contracts`)
- `graph` (`graph`, local `issue-dependency-graph`, `--open`, `--issue`, `--repo`)

## Autopilot routes

Catalog `autopilot.doctor`, `autopilot.start` (with `--runs`, `--checks`, `--engine`, `--label`, `--issues`, `--issue`, `--mode`, `--report`, `--decisions`, `--intake`, `--share`, `--agent`, hidden `--pool`, `--auto-update`), `autopilot.suite` (`--command`, `--timeout` `0..120`), `autopilot.status` (`--all`, `--json`), `autopilot.logs` (`issue`, `--issue`, `--follow`, `-f`, `--lines` `1..5000`, `--json`), `autopilot.stop`, `autopilot.observe`, `autopilot.auto`, `autopilot.off`, `autopilot.trust`, `autopilot.untrust`, `autopilot.add`, `autopilot.release`, `autopilot.intake`, `autopilot.graph`, `autopilot.report`, `autopilot.regressions`, `autopilot.investigate`, `autopilot.alerts`, `autopilot.alert`, and `autopilot.check-base`. [Autopilot launcher](autopilot-launcher.prompt.md) and [Autopilot alerts](autopilot-alerts.prompt.md) own execution.

## Regression scan

Register `autopilot.regressions`, prefix `autopilot regressions`, local `autopilot-regressions`, no operands, Boolean `--json` and text `--file`. Form: `pdd autopilot regressions [--json] [--file PATH]`. Description: Read core merge history and GitHub regression evidence; optionally save a local report, without GitHub writes or reverts.

## Daily investigation

Register `autopilot.investigate`, prefix `autopilot investigate`, local `autopilot-investigate`, no operands, text `--date`, Boolean `--json`, Boolean `--write-issues`, and integer `--max-issues` (`1..20`). Form: `pdd autopilot investigate [--date YYYY-MM-DD] [--json] [--write-issues] [--max-issues N]`. Description: Run the deterministic 4-bucket Autopilot incident investigator against local history, post-merge regressions, flakes, and report drafts (read-only by default; pass --write-issues to auto-file deduplicated strong-evidence GitHub issues up to --max-issues N).

## Metrics, shell, help, and version routes

- `metrics`, `metrics.stages`, `metrics.skills`, `metrics.full`, `metrics.on`, `metrics.off`
- `completion` (`completion bash|zsh`)
- `help` (`pdd`, `pdd --help`, `pdd -h`, `pdd help`, `pdd help prompting`, topic `prompting`)
- `version` (`--version`, quiet `-V`) and `version.detailed` (`-VV`)

## Help text

Export the frozen `PUBLIC_HELP_TEXT` object with `heading`, `usageLine`, `quickStartLines`, `groups`, `focusedHelpLines`, `closingLines`, `learnLines`, and `promptingLines`. Keep every rendered non-installation-path line of root help and `promptingLines` within 80 columns (`Skill:` and `Prompting guide:` print full local package paths). `usageLine` shows both direct execution (`pdd <PROMPT.md|STORY|.> [args...]`) and subcommands (`pdd <command> [options]`). Quick start highlights the 4-step workflow (`pdd setup`, `pdd init`, `/pdd`, `pdd prove`), and `Core PDD workflow` leads with `pdd <PROMPT.md|STORY|.>` on the Prompt Interpreter. Groups have zero duplicate entries across groups and zero user-facing `sim`/`simulate`/`Simulator` wording. Groups order human-first: `Core PDD workflow`, `Product & graph (pdd product --help)`, `Autopilot (pdd autopilot --help)`, `Cloud accounts (pdd accounts --help)`, and `Metrics, shell & help`.

## Learn PDD

The catalog owns the Learn PDD and `pdd help prompting` templates; the CLI substitutes `PACKAGE_ROOT` without reading files.

```text
In PDD, prompts are the source. Code follows the prompts.
1. Orient: run pdd status [--changed] for prompts, Stories, and Feature Map.
2. Prompt: prompts/NAME.prompt.md — plain English rules + ## Dependencies.
3. Story & Test: user_stories/STORY.md (## Acceptance criteria) +
   tests/STORY.json (or tests/runtime/ when native tests live in tests/).
4. Check: run pdd lint first (offline, 0 AI), then pdd test STORY.
5. Review: review each changed prompt in chat or GitHub PR review.
6. Build & Prove: code from approved prompts, then run pdd prove.
```

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- [Argument parser](argument-parser.prompt.md) and [Runtime seam](runtime-seam.prompt.md) consume the catalog contract.
