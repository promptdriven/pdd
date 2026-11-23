# Register PDD Simulator MCP tools with coding agents

Own `src/agent-mcp-setup.mjs`. Export async `setupAgentMcp({env, packageRoot}, {stdin, stdout, stderr, confirm, interactive, yes})`, returning exit code `0` or `1`.

## Domain decisions

- **Supported agents and honest detection (zero subprocesses):**
  - **Codex:** `$CODEX_HOME/config.toml` (else `$HOME/.codex/config.toml`), TOML `[mcp_servers.pdd]` (`command`, `args`, `default_tools_approval_mode = "approve"`, `tool_timeout_sec = 600`). Detected by existing config dir/file or `codex` executable on `PATH`.
  - **Claude Code:** `$CLAUDE_CONFIG_DIR/.claude.json` (else `$HOME/.claude.json`), JSON `/mcpServers/pdd` (`type: "stdio"`, `command`, `args`). Detected by existing config dir/file or `claude` executable on `PATH`.
  - **Gemini CLI:** `$HOME/.gemini/settings.json`, JSON `/mcpServers/pdd` (`command`, `args`, `trust: true`, `timeout: 600000`). Detected **only** by existing `$HOME/.gemini/settings.json` or `gemini` executable on `PATH` — never by bare `$HOME/.gemini/` alone (which Antigravity also creates).
  - **Antigravity (`agy`):** `$HOME/.gemini/config/mcp_config.json`, JSON `/mcpServers/pdd` (`command`, `args`). Detected **only** by existing `$HOME/.gemini/config/mcp_config.json`, `$HOME/.gemini/antigravity-cli`, or `agy` executable on `PATH` — never by bare `$HOME/.gemini/config`.
- **Pinned command:** `command = process.execPath`, `args = [resolve(packageRoot, 'bin/pdd.mjs'), 'mcp']`.
- **Stale PDD entry refresh vs unrelated conflict:**
  - If an existing `pdd` entry already matches `wanted`, skip it (no change).
  - If an existing `pdd` entry is a stale PDD MCP registration (references `pdd` / `pdd.mjs` with `'mcp'` arg, e.g. from an older Node or package location), plan an in-place update preserving custom user keys (such as `env` in JSON via `{ ...existing, ...wanted }` or extra non-PDD lines inside TOML `[mcp_servers.pdd]`, validated through the TOML parser).
  - If an existing `pdd` entry is an unrelated server, fail that agent cleanly without modifying it.
- **Per-agent error & symlink isolation:**
  - Check symlinks strictly on the config file and its agent config directory (stopping before `$HOME` / OS roots so symlinked `/var` or home mounts never false-fail).
  - A symlink on one agent emits `pdd setup: warning: ...` to stderr and skips only that agent (exit stays `0` if no hard error occurred).
  - A malformed config or conflicting non-PDD entry on one agent emits a clear `pdd setup:` diagnostic to stderr, sets `hadError = true`, and still proceeds for healthy agents.
- **Consent (`--yes` means YES) and atomic writes:**
  - Show exact per-agent previews for all planned PDD Simulator MCP tool changes.
  - When `yes === true`, apply previewed changes without asking.
  - When `!yes && !interactive`, skip without writing.
  - When `!yes && interactive`, ask once `Register these PDD Simulator MCP tools? [y/N] `; only trimmed case-insensitive `y` consents.
  - Re-verify path safety and unchanged original bytes immediately before writing; write atomically (`0o600` for new files, preserving existing mode) into `0o700` parent directories.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses Layer-0 `src/shared/atomic-fs.mjs` and the vendored TOML parser `src/vendor/smol-toml/parse.js`.
- [CLI](pdd-cli.prompt.md) invokes `setupAgentMcp` during `pdd setup`.
