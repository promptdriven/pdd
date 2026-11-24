# Local PDD command boundary

PDD supplies a single `/pdd` skill (`$pdd` in Codex, `/pdd` in Claude Code) and local CLI commands for your coding-agent workflow. Keep `pdd` as the command name. Provide local discovery and offline verification without private dependencies.

The local command surface includes help (root help, known local command help, and the `help prompting` topic), `--version` (also `-V`), `-VV`, `completion bash|zsh`, `setup`, `init`, `status`, `lint`, `prove`, `files`, `owner`, `update`, `contracts`, `jobs`, `mcp`, `upgrade`, `accounts`, `product`, `graph`, `autopilot`, and `metrics`. There is no `session` command and no `pdd workflow` command: people open Codex, Claude Code, Gemini CLI, or Antigravity as usual and invoke `/pdd` (or `$pdd`), use `pdd prove` for base-vs-head proof, or run `pdd autopilot` for headless background issue runs. Unknown, excluded, or removed commands (including with help flags) refuse clearly with exit 2 before effects.

Keep one catalog authoritative for help, parser, and completion. Parse before local reads. Success returns 0; unsupported syntax 2; local filesystem or check failure 1. Do not echo untrusted input. Local discovery reads do not create project files; [project setup](project-setup.prompt.md) (`pdd init`) writes its 4-line instruction block on request. [Autopilot settings](autopilot.prompt.md) reads and atomically updates repository `pdd.json`. On explicit setup consent (`--yes` or interactive y/N), [agent MCP setup](agent-mcp-setup.prompt.md) registers only the previewed PDD Prompt Interpreter MCP server entry in detected user configs. Package metadata/lock depends only on the bundled `@promptdriven/runtime-client` package, retains bin `pdd`, includes complete docs/skills/example assets, and avoids lifecycle scripts.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories.
- [Stateless proof](prove.prompt.md) owns `pdd prove` execution (offline merge-base verification and isolated base-vs-head bug-contrast proofs with zero interpreter calls).
- [Codex readability and quality lint](codex-lint.prompt.md) owns `pdd lint --codex` read-only checks.

## Caller and installer navigation

pdd pastes no guide or skill text: help names the paths of the installed PDD skill (`skills/pdd/SKILL.md`) and Prompting guide (`skills/pdd/references/prompting.md`) and gives a short summary ([Learn PDD](command-catalog.prompt.md#learn-pdd)), and the agent loads the skill and references on demand.

The package ships one visible skill `skills/pdd/` and retires split skills (`pdd-autopilot`, `pdd-check`, `pdd-merge`, `pdd-setup`, `pdd-prompting`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`, `pdd-graph`). `pdd setup` installs missing skills through [skills install](skills-install.prompt.md) (respecting Claude Code plugin installs while still cleaning marked retired split skills, or targeting optional `--skills-dir`). Normal CLI commands refresh existing `.pdd-skill.json`-marked user skill folders once per CLI version without touching unmarked folders or symlinks, and `pdd upgrade [--main]` ([CLI upgrade](cli-upgrade.prompt.md)) updates a user-owned global npm or Volta `@promptdriven/pdd` installation and refreshes `.pdd-skill.json`-marked user skills. pdd writes skills only to user skill folders (`~/.agents/skills/`, existing marker-owned `~/.codex/skills/` or `$CODEX_HOME/skills/`, `~/.claude/skills/` or `$CLAUDE_CONFIG_DIR/skills/`, `~/.gemini/config/skills/`, or explicit `--skills-dir`), never to the person's repo.

## PDD interpreter

The PDD interpreter is the hosted service that checks and runs prompts. Every line that pdd writes itself for a person calls it "the PDD interpreter", or "the interpreter" after the first mention. Forbidden: "PDD runtime" or "the runtime" for this service in user-facing lines.

Machine-read words keep "runtime": schema ids `prompt-runtime.*`, `DEFAULT_RUNTIME_URL`, `PDD_RUNTIME_URL`, `~/.pdd/runtime`, `runtime-capture-v1`, local dispositions `runtime-check` and `runtime-try`, `Runtime interface` block labels, and verbatim server messages. The summary line is `Prompt tests (<story>): …` ([Prompt tests words](prompt-tests-words.prompt.md)).

Hosted interpreter operations (`pdd test`, `pdd lint --remote`, direct `pdd <PROMPT.md|STORY|.>`, and Try tools in `pdd mcp`) call the PDD interpreter with the user's `gh` token via the [Runtime seam](runtime-seam.prompt.md). The token stays in memory and never appears in files, logs, argv, URLs, or errors. `pdd -VV` ([detailed version](interpreter-version.prompt.md)) is a bounded metadata-only GET with zero AI calls. `pdd accounts` ([Cloud accounts CLI](accounts-cli.prompt.md) and [Cloud accounts and login pool](login-pool.prompt.md)) communicates only with PDD Cloud Accounts endpoints. No other command calls a hosted service.

## Command words

Every line that pdd writes itself for a person names commands with the [Names](command-catalog.prompt.md#names) words (`pdd test`, `pdd lint`) and direct prompt/Story execution (`pdd <PROMPT.md|STORY|.>`). A wrapper error of `pdd <PROMPT.md|STORY|.> --cli` or `--serve` starts with `pdd:`. Forbidden in user-facing source lines: `pdd check`, `pdd try`, `pdd try:`, `pdd sim`, or `pdd simulate`. Only the [removal lines](argument-parser.prompt.md#removed-names) name removed commands.

Machine-read words keep `check` and `try` where servers, saved files, and scripts depend on them: wire commands `check` and `try`, `/v1/try/…` paths, `.pdd/try`, `PDD Try launcher v1`, `x-pdd-try-*` headers, `tries/` records, and local dispositions `runtime-check` and `runtime-try`.

The package may include a licensed, attributed vendored public TOML parser under `src/vendor/` for safe config validation. It requires no npm install or registry access at runtime.
