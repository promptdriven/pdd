# Own-agent adapters

Own `src/agent-adapters.mjs`: PDD's local agent CLI discovery, shared credential-status interpretation, and direct subprocess runner (`agents.list` and `agents.run`). Simulator chat turns (`askAgent`, response parsing, fill validation, and temporary read-only overlays) live in [`src/runtime/agent-ask.mjs`](agent-ask.prompt.md).

Export asynchronous `discoverAgents({cwd,env,run,definitions,workspace})`, pure `parseAgentAuthStatus({agent,result})`, and `runAgentProcess(command,args,{cwd,env,input='',signal,timeoutMs=120000,maxBytes=131072})`. `run(command,args,{cwd,env,input,signal,timeoutMs,maxBytes})` is a direct subprocess port without a shell returning `{code,stdout,stderr}`, with `runAgentProcess` as its default implementation; cancellation sends `SIGTERM` to the process group (falling back to the child) followed by `SIGKILL` after 500 ms, and enforces `timeoutMs` (`timeout`) and `maxBytes` (`output limit`).

Discovery uses supplied private `definitions`, or loads them through [`loadAgentDefinitions`](agent-config.prompt.md) (defaults: Codex, Claude, and Gemini in that order). Return only metadata `{id,name,state,detail?}`, never `kind`, `command`, `env`, or raw auth output. States are `ready`, `available`, `signed_out`, `quota`, `not_installed`, and `error`. Check installation with `--help` and authentication with cheap status commands (10 s timeout, 128 KiB help cap, 16 KiB auth cap); never spend a model call or modify `process.env`. For custom definitions, `kind` selects the adapter (`codex`, `claude`, `gemini`) and `command` runs with a fresh child-only merge `{...env, ...overrides}`.

## Bounded workspace discovery

When `workspace` or [`workspace.policy({root: cwd})`](runtime-entry.prompt.md) ([workspace boundary](runtime-workspace.prompt.md)) has `configured: true`, return `{id, name, state: 'error', detail: 'Bounded agent connection is unavailable: packet-only context cannot be established.'}` for each supplied or default agent without starting any subprocess.

## Shared credential-status interpretation

Export pure module function `parseAgentAuthStatus({agent,result})`, returning `ready`, `signed_out` or `unavailable`. Both discovery and workflow readiness use this owner; neither keeps its own auth parser. Ready means credentials configured, not that a token is unexpired or a provider request would succeed. Never run a model request to prove readiness.

Require an integer process exit code and string stdout/stderr. Codex reads both streams after removing ANSI controls: exit 0 with a `Logged in` or `API key configured` marker is ready. The latter may be followed by masked key text and `Authentication is checked when you send a request.`; never expose any of that output. `Not logged in`, `Not signed in`, or a login/sign-in-required marker on exit 0 or 1 is signed_out. A negative marker by itself is signed_out, not contradictory; both an independent affirmative marker and a negative marker together are unavailable; negative markers on exit 2 or above, nonzero success text, unrelated output and malformed results are unavailable. Claude requires strict JSON stdout with Boolean loggedIn: true on exit 0 for ready, or Boolean false on exit 0 or 1 for signed_out. Strings, missing fields, banner-prefixed JSON, malformed data and nonzero success payloads are unavailable. Unknown agent kinds are unavailable.

Discovery checks `--help` read-only capability flags first (`--sandbox` for Codex; `--safe-mode`, `--tools`, and `--permission-prompts` for Claude, reporting `The agent help command failed.` on nonzero exit or `Update this agent to a version with the required read-only controls.` when a flag is absent), runs `codex login status` or `claude auth status --json`, and maps `ready`/`signed_out` unchanged and `unavailable` to `error`. Gemini inspects `--help` for `--approval-mode`, `--admin-policy`, `--extensions`, `--allowed-mcp-server-names`, and `--output-format` (reporting `Gemini Try read-only capability discovery failed (--help).` on nonzero exit or `Gemini Try read-only mode requires <flag>; update Gemini CLI.` when a flag is absent) and otherwise returns `state: 'available'`, `detail: 'Installed; sign-in is checked when you send a message.'`, never falsely `ready`.

The native process port classifies `ENOENT` conservatively with Boolean `error.executableMissing`. It is true only when `cwd` is an existing directory and `command` has no installed candidate on the exact effective search path. A missing `cwd`, a present executable with a missing shebang interpreter, a broken symlink, or an unreadable/uncertain lookup makes it false. Inspect only `cwd` and candidate installation metadata, never agent credential files, without invoking help, login, or a model, changing `PATH`, or exposing paths. Both discovery and workflow readiness report `not_installed` / missing only when `error.code === 'ENOENT' && error.executableMissing === true`.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime context for bounded-workspace discovery refusal via [`src/runtime-seam.mjs`](runtime-seam.prompt.md).
- [Local agent configuration](agent-config.prompt.md): required generation context for `loadAgentDefinitions`.

## Caller navigation

[`src/runtime-seam.mjs`](runtime-seam.prompt.md) binds `discoverAgents` and `runAgentProcess` as the host agent ports for [`src/runtime/agent-chat.mjs`](agent-chat.prompt.md) and [`src/runtime/agent-ask.mjs`](agent-ask.prompt.md).
