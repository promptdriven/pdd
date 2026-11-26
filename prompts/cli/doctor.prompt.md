# Host health check (`pdd doctor`)

Own `src/setup/doctor.mjs` (Layer-1 `setup`), exporting `collectDoctorReport(options, ports)`, `formatDoctorReport(report, options)`, and `runDoctor(options, ports)`.

`pdd doctor [--json]` is a fast, universal, **100% read-only** host health check covering the running `pdd` CLI and Node.js runtime, competing `pdd` installs and login-subshell `PATH` parity, user agent skills, agent MCP configs, and GitHub CLI (`gh`) sign-in.

## Domain decisions

- **100% read-only guarantee:** `collectDoctorReport` and `runDoctor` MUST NEVER create, write, modify, chmod, rename, or delete any file or directory in `$HOME`, `$PDD_STATE_DIR`, `cwd`, or the repository. Never invoke `gh` when neither `GH_TOKEN`/`GITHUB_TOKEN` nor a `hosts.yml` config file is present (to prevent `gh` from creating `$HOME/.local/state/gh`), and pass `GH_NO_UPDATE_NOTIFIER=1` whenever `gh` is invoked.
- **Layer-1 `setup` purity:** import only Node stdlib, `src/shared/*`, `src/path-diagnostic.mjs`, and `src/setup/*` — zero imports from `core`, `autopilot`, `accounts`, or `cli`.
- **Fail-safe host tolerance:** never crash on missing `/bin/zsh`, missing `/bin/bash`, missing `gh`, missing `$HOME` directories, unreadable files, 0-byte configs, malformed JSON/TOML, symlinks, or hanging child binaries. Bound every subprocess check to `<= 1500` ms (`probeTimeoutMs`, default `1500`) and never interpolate paths or user strings into shell command strings.
- **Five diagnostic checks:**
  1. **CLI & Node runtime (`runtime`):** read running `pdd` version from `packageRoot/package.json`, install kind, canonical binary path, and Node.js version (`ports.nodeVersion ?? process.versions.node`). Require Node `>= 22.16.0` (matching `package.json` `engines.node`). Status is `'ok'` when `pdd` version is readable and Node `>= 22.16.0`, else `'error'`.
  2. **Installs & shell PATH (`installs`):** invoke [PATH & host install diagnostics](path-diagnostic.prompt.md) `diagnoseHostInstalls({ packageRoot, currentBin, cwd, env, home, checkLoginShells: true, probeTimeoutMs }, ports)`. Status is `'ok'` when `!diagnosis.hasConflict`, else `'warn'` (actionable issue) with one finding and safe cleanup command per duplicate install, PATH shadowing entry, login-shell split, and unscoped npm `"pdd"` conflict.
  3. **Agent skills (`skills`):** inspect user skill folders read-only (when a valid absolute `$HOME` or explicit override exists): `~/.agents/skills` (required when Codex or Gemini CLI is detected), `~/.claude/skills` (or `$CLAUDE_CONFIG_DIR/skills`, respecting Claude Code plugin installs via `hasClaudePluginInstall`), `~/.gemini/config/skills` (when present or Antigravity is detected), and `~/.codex/skills` (plus `$CODEX_HOME/skills` when set and distinct). Detect current `pdd` skill, stale (`older` or `differs`) copies, missing primary copies, and any leftover retired PDD skill folders (`RETIRED_SKILL_NAMES`). Suggest `pdd setup` for marked/missing/marked-retired copies, `npx skills add promptdriven/pdd -g` for unmarked stale copies, and explicit manual removal for unmarked retired folders (never sending users into an unfixable `pdd setup` loop). Status is `'ok'` when at least one primary root (or Claude plugin) is current and zero stale, missing-required, or retired skills exist, else `'warn'`.
  4. **Agent MCP config (`mcp`):** inspect detected Codex (`$CODEX_HOME/config.toml` / `~/.codex/config.toml`), Claude Code (`$CLAUDE_CONFIG_DIR/.claude.json` / `~/.claude.json`), Gemini CLI (`~/.gemini/settings.json`), and Antigravity (`~/.gemini/config/mcp_config.json`) configs read-only (same detection rules, `CODEX_HOME`/`CLAUDE_CONFIG_DIR` resolution, and boundary-scoped symlink checks as [agent MCP setup](agent-mcp-setup.prompt.md)). Classify each detected agent as:
     - `'ok'`: regular file, valid JSON/TOML, `pdd` MCP entry exists with a valid executable command (missing absolute `command` binary is `'stale'`) and resolves (via realpath / Volta shim / pnpm wrapper) to the current `pdd` install (or bare `pdd` only when `PATH` currently selects this `pdd` with zero install conflict).
     - `'symlink'`: config file or parent within the agent boundary is a symlink (advisory — reported clearly, does not cause exit `1` on its own).
     - `'missing'`: config file absent or missing the `pdd` MCP entry (actionable issue, fix: `pdd setup --yes`).
     - `'stale'`: `pdd` MCP entry points to a different or missing `pdd` install or missing command binary (actionable issue, fix: `pdd setup --yes`).
     - `'empty'`: config file is 0-byte, whitespace-only, or UTF-8 BOM-only JSON (actionable `'warn'`, `code: 'mcp-empty'`, fix: `pdd setup --yes`, aligned with [agent MCP setup](agent-mcp-setup.prompt.md) `#3646` — deduplicated with `'missing'` and never instructing manual editing or file deletion). Also strip a leading UTF-8 BOM before parsing non-empty JSON configs.
     - `'malformed'` / `'unreadable'` / `'non-regular'`: parse error, I/O error, or non-regular file (actionable issue; `'non-regular'` recommends moving/removing the non-regular path before `pdd setup --yes`).
     When zero supported agents are detected, status is `'ok'` with an empty `agents` array.
  5. **GitHub CLI (`gh`):** read-only bounded check (`1500` ms, `maxBuffer: 65536`) for hosted interpreter runs (`pdd test`, `pdd <PROMPT.md|STORY>`). Recognizes `GH_TOKEN`/`GITHUB_TOKEN` without spawning `gh`; checks `gh` on `PATH` and `hosts.yml` (including `%APPDATA%\GitHub CLI\hosts.yml` on `win32`) before invoking `gh auth token` with `GH_NO_UPDATE_NOTIFIER=1`. Status is `'ok'` when authenticated, else `'advisory'` (`method`: `'missing'`, `'signed-out'`, or `'timeout'`) with consistent remediation (`gh auth login` or install hint). Because local offline PDD works without `gh`, an unauthenticated `gh` is an advisory and never causes exit `1`.
- **Exit code contract:**
  - Exit `0`: all checks pass cleanly (advisories such as optional `gh` sign-in or intentional symlinked MCP config may still be shown).
  - Exit `1`: one or more actionable problems are detected (incompatible Node `< 22.16.0`, unreadable CLI metadata, duplicate/shadowed `pdd` installs, login-shell `PATH` split, unscoped npm `"pdd"`, missing/stale/retired agent skills, or missing/stale/0-byte/malformed/unreadable/non-regular MCP config).
- **Output format:**
  - Human output (`json: false`): concise ~10–15 line scannable summary (`✓` pass, `⚠` actionable problem, `–` advisory) with paths inside `$HOME` shortened to `~/...`, exact 1-line fix commands underneath each problem, and all untrusted config/path text sanitized against ANSI escapes and control characters/newlines. No ANSI escape codes. Written to `stdout` on both exit `0` and exit `1`.
  - JSON output (`json: true`): pretty-printed `pdd.doctor.v1` JSON object with trailing newline written to `stdout` on both exit `0` and exit `1`.

## Public contract

- `collectDoctorReport({ cwd, env, packageRoot, home, probeTimeoutMs }, ports)` returns the `pdd.doctor.v1` report object:
  - `schema_version`: `'pdd.doctor.v1'`
  - `ok`: boolean (`exit_code === 0`)
  - `exit_code`: `0 | 1`
  - `summary`: `{ issues: number, advisories: number }`
  - `checks`: `{ runtime, installs, skills, mcp, gh }`
  - `findings`: array of `{ check, severity: 'error' | 'warn' | 'advisory', code, message, path: string | null, remediation: string | null }`
  - `remediations`: deduplicated array of actionable remediation command strings
- `formatDoctorReport(report, { home })` returns a newline-terminated plain-text summary string.
- `runDoctor({ cwd, env, packageRoot, home, json = false, probeTimeoutMs }, ports)` collects the report, writes JSON or formatted text to `ports.stdout` when provided, and returns `{ exitCode, report, output }`.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses [PATH & host install diagnostics](path-diagnostic.prompt.md), [skills install](skills-install.prompt.md), [install kind](install-kind.prompt.md), `src/shared/package-root.mjs`, and `src/shared/toml/parse.js`.
- Navigation only: [CLI](pdd-cli.prompt.md) dispatches `pdd doctor [--json]` to this module.
