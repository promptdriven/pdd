# Multi-harness login pool

Own `src/login-pool.mjs`. Export `resolvePoolPath({env, poolPath})`,
`loadLoginPool({cwd, env, poolPath, fallbackAgent}, ports)`,
`loginEnvironment(baseEnv, login)`, `isQuotaExhaustionMessage(text)`,
`readPoolCooldowns({stateRoot, now}, ports)`,
`markLoginExhausted({stateRoot, loginId, resetAt, reason, now}, ports)`,
`clearPoolCooldowns({stateRoot}, ports)` and
`selectPoolLogin({cwd, env, poolPath, fallbackAgent, stateRoot, allowLimited}, ports)`.

## Pool configuration

The pool orders local agent logins (`codex`, `claude`, `gemini`, `agy`) on one
machine without copying or storing tokens. Each login points only to a local
program and profile folder (`CODEX_HOME`, `CLAUDE_CONFIG_DIR`, `GEMINI_CLI_HOME`
or `ANTIGRAVITY_APP_DATA_DIR`).

`resolvePoolPath` uses an explicit `poolPath` (expanding `~/` with `env.HOME`),
else `${XDG_CONFIG_HOME || ~/.config}/pdd/pool.json`, else `~/.pdd/pool.json`.
An explicit `poolPath` of `off` or `none` disables file discovery and uses only
the single fallback agent. When an explicit file path is missing, symlinked,
larger than 65,536 bytes or invalid JSON, throw `Error("Invalid login pool: ...")`.
Read regular files with `O_NOFOLLOW`.

A pool file is a JSON object with:
- optional `reset`: only `"never"` is accepted; any other value throws so
  Autopilot never spends reset credits;
- optional `weeklyStopPercent`: finite number in `(0, 100]`, default `97`;
- `logins`: non-empty array of at most 24 objects, each with `kind`
  (`codex`, `claude`, `gemini` or `agy`), optional unique `id`
  (`[A-Za-z0-9._-]+`, default `kind`), optional `command`, optional `model`,
  optional `plan` (`plus`, `pro`, `team`, `max`, `free` or text), optional
  Boolean `credits` and `paused`, optional profile folder (`codexHome`,
  `claudeConfigDir`, `geminiCliHome`, `appDataDir` or `configHome`, with `~/`
  expanded), and optional non-secret `env` map. Reject secret-named keys in
  `env` (`*_TOKEN`, `*_SECRET`, `*_API_KEY`, `*_PASSWORD`, `*_CREDENTIAL*`).

When no pool file exists, `loadLoginPool` returns a single-entry pool synthesized
from `fallbackAgent` (or default `codex`) and its ambient profile folder with
`configured: false`.

## Isolation, quota classification and cooldowns

`loginEnvironment(baseEnv, login)` returns a copy of `baseEnv` with unrelated
provider config variables (`CODEX_HOME`, `CLAUDE_CONFIG_DIR`, `GEMINI_CLI_HOME`,
`ANTIGRAVITY_APP_DATA_DIR`) removed, the selected login's own profile folder set
when present, and `login.env` applied.

`isQuotaExhaustionMessage(text)` returns `true` for account quota, usage-limit,
rate-limit, spend-control and out-of-credits messages (`out of credits`, `credit
balance is too low`, `insufficient quota`, `exceeded your current quota`, `quota
exceeded`, `usage limit`, `rate limit`, `rate_limit`, `too many requests`, `429`,
`spend control`, `spending limit`, `weekly limit`), and `false` for test
diagnostics or transient `5xx`/overloaded server errors.

Cooldowns live in `join(stateRoot, "login-pool.json")` (atomic rename, mode
`0600`). `markLoginExhausted` sets `until` to `resetAt` when `resetAt > now`,
else `now + 30 * 60 * 1000` (30-minute bounded retry window when reset time is
unknown). `readPoolCooldowns` drops expired entries (`until <= now`).

## Selection and 97% weekly stop protection

`selectPoolLogin` walks non-paused logins in order:
1. Skip logins with an active cooldown (`until > now`), recording `{id, until, reason}`
   in `cooling`.
2. Build `loginEnvironment` and check local sign-in (`codex login status`,
   `claude auth status --json`, `agy models` via `checkWorkflowAgents`, or
   `gemini --version` plus `GEMINI_API_KEY`, `GOOGLE_API_KEY`,
   `GOOGLE_GENAI_USE_VERTEXAI=true`, `GOOGLE_GENAI_USE_GCA=true`, or an
   `oauth_creds.json` `refresh_token` in `.gemini/` or the profile root;
   replaceable via `ports.probeLogin`). Unsigned logins go to `unavailable`.
3. For `codex`, call `readCodexLimits` with `weeklyStopPercent` (default `97`).
   - `limited` marks the login exhausted until `limits.resetAt` (or 30 minutes)
     and moves to the next login (unless `allowLimited` is set for preflight
     selection when all logins are limited).
   - `unknown` on a Pro or extra-credits account (`plan === "pro"` or
     `credits === true`) fails closed onto a 30-minute cooldown instead of
     risking paid extra credits.
4. Return `{state: "ready", configured, poolPath, poolSize, login, agent, env}`
   for the first healthy login.
5. When none is ready, return `{state: "exhausted", configured, poolPath,
   poolSize, resetAt, cooling, unavailable}`, where `resetAt` is the earliest
   cooldown timestamp or `null`.

## Dependencies

- [Read Codex account limits](codex-limits.prompt.md) supplies the read-only
  primary/weekly rate-limit check.
- [Agent adapters](agent-adapters.prompt.md) and
  [workflow agents](workflow-agents.prompt.md) supply local CLI sign-in probes.
