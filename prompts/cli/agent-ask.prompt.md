# Simulator agent turn

Own `src/runtime/agent-ask.mjs`. Export asynchronous `askAgent({agent,definition,cwd,env=process.env,context={},entries=[],supportsApply=false,supportsRun=false,workspace,signal,run,timeoutMs=120000}={}, ports={})`, asking one chosen local agent CLI to explain or prepare a Try input without executing a filled input or switching providers after failure.

`run` (`input.run ?? ports.run ?? ports.runAgentProcess ?? ports.agents?.run`) is the injected subprocess port `(command, args, {cwd, env, input, signal, timeoutMs, maxBytes}) => Promise<{code, stdout, stderr}>` supplied by the host caller. When a turn reaches subprocess execution without a bound `run` function, throw an `Error` (`unboundPort: true`) naming the unbound agent process port.

## Bounded workspace invocation

When a [workspace policy](runtime-workspace.prompt.md) is configured (`workspace ?? (cwd ? loadRuntimeWorkspace({root: cwd}) : null)` has `configured: true`), only packet-supplied project context is permitted. Read-only sandboxes, small stdin, disabled write tools, Codex ignore-rules/feature overrides, Claude Read/Grep/Glob permissions, and the Gemini deny-all overlay do not suppress repository reads or automatic project/instruction loading. Because current native controls cannot establish packet-only context, return `{say, fill: null, error: {state: 'error', message: 'Bounded agent connection is unavailable: native tool and automatic context controls cannot establish packet-only context.'}}` before any authentication, help probe, or model process, for both built-in and custom definitions.

## Read-only CLI invocation and temporary overlays

Accept optional private `definition` (`{id, name, kind, command, env}`); `kind` selects the adapter (`codex`, `claude`, or `gemini`, rejecting any other kind with `Choose Codex, Claude or Gemini.`), `command` overrides the executable, `name` overrides the diagnostic display name (`Codex`, `Claude`, `Gemini`), and `definition.env` merges into a fresh child-only copy of `env` without mutating `process.env`. An already-aborted `signal` returns `error` (`The agent request was cancelled.`) before starting a process.

Each question starts a fresh process in `cwd`, without resume, model/effort overrides, or user configuration writes:

- **Codex:** invoke `exec --sandbox read-only --ephemeral --color never --ignore-rules -c approval_policy="never" -c web_search="disabled" -c mcp_servers={}` with `-c features.<name>=false` for `hooks`, `plugins`, `apps`, `browser_use`, `browser_use_external`, `browser_use_full_cdp_access`, `computer_use`, `multi_agent`, `multi_agent_v2`, `shell_tool`, `unified_exec`, `code_mode`, and `code_mode_host`, reading stdin (`-`). Never enumerate MCP servers or write per-server `.enabled=false` keys. Only a Codex configuration-startup failure (nonzero exit with empty stdout whose first nonempty stderr line is a config-loading or explicit unknown-feature error naming one disabled `features.<name>`) retries once without that single feature flag while keeping all other restrictions; never retry quota, sign-in, or provider errors, or a second unknown feature.
- **Claude:** invoke `-p --safe-mode --tools Read,Grep,Glob --permission-mode plan --permission-prompts none --strict-mcp-config --no-chrome --no-session-persistence --output-format json`.
- **Gemini:** probe `<command> --help` (10 s timeout, 128 KiB cap) for the required read-only flags (`--approval-mode`, `--admin-policy`, `--extensions`, `--allowed-mcp-server-names`, `--output-format`, matching host agent discovery): return `Gemini Try read-only capability discovery failed (--help).` on nonzero exit or `Gemini Try read-only mode requires <flag>; update Gemini CLI.` when a flag is absent, before creating overlays or calling a model. Refuse before a model call (`Gemini system policy prevents the private deny-all policy.`) when the OS Gemini system `policies` folder contains any `.toml` file. Read existing system `settings.json` (<=1 MiB JSON object when present) from `GEMINI_CLI_SYSTEM_SETTINGS_PATH` or the OS system directory, preserve original model/auth fields and `GEMINI_CLI_SYSTEM_DEFAULTS_PATH`, and write a mode-0700 temporary directory containing mode-0600 `settings.json` (`tools.core=[]`, `tools.allowed=[]`, empty `discoveryCommand`/`callCommand`, disabled `hooksConfig.enabled`, `admin.{mcp,extensions,skills}.enabled`, `general.{enableAutoUpdate,enableAutoUpdateNotification}`, and `general.plan.{enabled,modelRouting}`) plus mode-0600 `deny.toml` (`toolName = "*"`, `decision = "deny"`, `priority = 999`), removing the temporary directory in `finally`. Also pass `--extensions none`, `--allowed-mcp-server-names pdd-disabled-<uuid>`, `-p "Answer the supplied Try question as strict JSON."`, `--approval-mode default`, `--admin-policy <deny.toml>`, and `--output-format json` so remote admin defaults cannot re-enable extensions or MCP servers.

## Secret scrubbing, diagnostics, and bounded packet

Give the chosen agent only the bounded stdin packet from [`buildAgentInput`](agent-packet.prompt.md) (<=24 KiB stdin, <=128 KiB stdout/stderr, default 120 s timeout) using scrubbed `context` and `entries` (`{entry, prompt_path, operation, input_schema}`) plus `supportsApply` and `supportsRun`. Recursively replace values under secret-named keys (`token`, `password`, `secret`, `api[_-]?key`, `authorization`, `cookie`, `credential`), nonempty values of secret-named `env` variables (including short values), PEM private keys, `gh*` / `github_pat_*` / `sk-*` tokens, `Bearer` credentials, `key=value` secret assignments, and URL userinfo with `[redacted]` before building stdin and on every returned text/structured field.

Map nonzero exits and process errors (`ENOENT` -> `not_installed`; rate/usage/quota/credits/capacity -> `quota`; not-logged/not-signed/sign-in/login-required/unauthorized/authentication -> `signed_out`; else `error`) to `{say: message, fill: null, error: {state, message}}`. Strip ANSI/control characters and secrets from the first nonempty error line (<=500 chars; fallback `The CLI exited without an error message.`), prefix `<Name> could not start: ` for `error` or the plain state sentence (`signed_out`, `quota`, `not_installed`), and append `Details: <log>` when appending scrubbed full stderr to `~/.pdd/runtime/agent-chat.log` (mode-0700 directories, mode-0600 regular file opened with `O_NOFOLLOW | O_NONBLOCK`, rejecting symlinks/FIFOs) succeeds, else `Local diagnostic log unavailable.`.

## Strict JSON reply and optional field validation

Decode Claude's `{result, is_error}` string wrapper (treating `is_error` as a failed invocation) and Gemini's `{response}` string wrapper without accepting markdown fences or surrounding prose; `SyntaxError` returns `The agent returned invalid JSON. No fields were applied.`. Require one JSON object containing only keys from `say`, `fill`, `apply`, `criterion`, `expect`, `save`, `next`, `run` with nonempty trimmed string `say` (otherwise return `The agent returned an invalid answer. No fields were applied.`).

Scrub the parsed object and validate optional fields independently, dropping invalid optional fields while keeping valid `say`:

- `fill`: `null` or exact `{entry, input}` where `entry` matches `entries`, `input` is a plain object containing no `$step_result` reference, and [`checkInput`](runtime-preflight.prompt.md) produces zero refusals and zero warnings after scrubbing; otherwise `fill` becomes `null`.
- `apply`: Boolean, retained only when `fill` is valid (`fill !== null` or `apply === false`).
- `run`: Boolean, retained only when `supportsRun && supportsApply`, `context.requestKind ?? 'chat'` is one of `'chat'`, `'own'`, `'walk'`, and either `run === false` or `apply === true && fill !== null`.
- `criterion`: `null` or a known ID from `context.criteria`.
- `next`: `null` or exact `{text, criterion}` with nonempty `text` <=200 chars and `criterion` `null` or known.
- `expect`: `null`, or (only when `result.fill` is non-null) exact `{text, checks}` (<=16384 UTF-8 bytes) with nonempty `text` <=500 chars and 1..32 `{target, path, value}` items (`target` in `['result', 'world']`, valid JSON Pointer `path` <=256 chars, and no `$step_result` in `value`).
- `save`: `null` or exact `{name, criterion, checks}` with nonempty `name` <=100 chars, `criterion` `null` or known, and 1..32 `{target, path}` items.

## Dependencies

- [Runtime workspace boundary](runtime-workspace.prompt.md): required generation context for `loadRuntimeWorkspace` bounded-mode refusal.
- [Agent packet](agent-packet.prompt.md): required generation context for `buildAgentInput` bounded stdin construction.
- [Runtime preflight](runtime-preflight.prompt.md): required generation context for `checkInput` fill validation.

<details><summary>Runtime interface</summary>

```json
{"kind":"native-only","status":"approved","prose_sha256":"531518f855702abe19934ec1ea850cb627b90dc39b4ce91a31b18de9cc871956","reason":"Prepares OS-specific Gemini temporary policy files, diagnostic log descriptors, and local CLI subprocess arguments executed through an injected host process port."}
```
</details>
