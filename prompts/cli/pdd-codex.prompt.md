# PDD Codex launcher

Own `bin/pdd-codex.mjs` and `src/pdd-codex.mjs`. Provide a dedicated `pdd-codex` command that launches the user's installed `codex` binary through the PDD Cloud `/v1/codex-gateway/backend-api` gateway without touching stock `codex` or `~/.codex/auth.json`.

## Core behavior

- **Executable entry (`bin/pdd-codex.mjs`):** Check `process.versions.node` major version is at least 22 before importing `src/pdd-codex.mjs`. Avoid static imports before the version check. Exit with the integer returned by `runPddCodexCli`.
- **Argument handling (`parsePddCodexArgs`):**
  - Parse optional leading `--account <label>` / `--account=<label>` and `--pdd-help` before `--` and before the first non-option argument; forward all remaining arguments verbatim to `codex`.
  - `pdd-codex logout` deletes `<runtime>/auth.json` and `<runtime>/lease.json` inside the shared runtime folder and revokes the cloud lease via `releaseCloudLease` without touching `~/.codex/auth.json`.
  - `pdd-codex login` prints instructions to enroll with `pdd accounts add --provider codex` (or use stock `codex login` for personal accounts) without touching `~/.codex/auth.json`.
  - Local `--version`, `-V`, `--help`, `-h`, `help`, and `completion` pass straight to `codex` without requiring a cloud lease.
  - Local `mcp add|remove|list|get` runs inside a temporary directory whose `config.toml` is symlinked to `~/.codex/config.toml` so MCP configuration edits write straight into `~/.codex/config.toml` without requiring a cloud lease.
- **Shared machine runtime folder with PID ref-counting (`acquireSharedRuntimeSession` / `releaseSharedRuntimeSession`):**
  - Use one `0700` directory per user under `join(resolvePddStateBase(env), 'codex-runtime')` (`~/.local/state/pdd/codex-runtime/pdd-codex-<uid>`, never under `/tmp` so Linux stock Codex creates helper binaries cleanly; overridable via `PDD_CODEX_RUNTIME_ROOT`), refusing symlinks or directories owned by another OS user.
  - Serialize acquisition and release with an atomic `mkdir` lock directory (with stale-lock recovery after 30 seconds).
  - Auto-create `~/.codex/`, empty `~/.codex/config.toml`, and baseline user folders (`sessions`, `archived_sessions`, `plugins`, `skills`, `rules`, `memories`) on brand-new machines via `ensureUserCodexHomeBaseline`, mirror user entries with `syncManagedCodexHomeLinks`, symlink `<runtime>/config.toml` directly to `~/.codex/config.toml`, and create `0700` `<runtime>/empty-subshell/`.
  - Track live sessions in `pids/<pid>`, sweeping dead PIDs via `process.kill(pid, 0)`. Reuse an existing valid `auto_rotate: true` `lease.json` + `auth.json` (> 5 minutes left) across concurrent sessions so 60–100 concurrent `pdd-codex` sessions share 1 runtime folder and 1 PDD Cloud lease.
  - When the last live `pdd-codex` process exits, immediately unlink `<runtime>/auth.json` and `<runtime>/lease.json` and call `POST /v1/accounts/leases/{lease_id}/release`.
- **Pinned `--account <label>` mode (`acquirePinnedRuntimeSession`):**
  - Use an isolated `0700` temporary directory (`pdd-codex-pin-*`) under the same runtime root (`resolveRuntimeRoot`) with `auto_rotate: false` so pinned runs never disturb concurrent shared sessions, and delete the temp directory + revoke the pinned lease on exit.
- **Gateway routing, subshell isolation, and background heartbeat:**
  - Strip `OPENAI_API_KEY`, `CODEX_API_KEY`, `CODEX_ACCESS_TOKEN`, `OPENAI_BASE_URL`, `PDD_CODEX_GATEWAY_GRANT`, and `CODEX_CONNECTORS_TOKEN` from the child environment, set `CODEX_HOME=<runtimeDir>`, and pass the revocable `pddg_*` grant token via `CODEX_CONNECTORS_TOKEN` to the spawned `codex` process so stock Codex's built-in `codex_apps` MCP client authenticates cleanly to `<backendApiUrl>/ps/mcp` without 401 errors.
  - Pass verified `-c` flags via `buildCodexGatewayCliArgs` (`cli_auth_credentials_store="file"`, `chatgpt_base_url`, `openai_base_url`, `sqlite_home`, `features.daemon_auto_start=false`, `features.shell_snapshot=false`, `shell_environment_policy.set.CODEX_HOME=<empty-subshell>`, `shell_environment_policy.exclude` covering `CODEX_CONNECTORS_TOKEN`, and compatibility aliases `model_providers.pdd_pool` / `model_providers.pdd_codex_gateway`). Never leak gateway URLs into `~/.codex/config.toml`.
  - While `codex` runs, periodically call `heartbeatCloudLease` (`POST /v1/accounts/leases/{lease_id}/heartbeat`) on an `.unref()`'d timer to keep the sliding TTL and org-membership verification fresh, stopping cleanly on exit or revocation.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Reuse Cloud Accounts transport and symlink helpers from [login-pool.prompt.md](login-pool.prompt.md) and secret redaction from [secret-redaction.prompt.md](secret-redaction.prompt.md).
