# Choose an available workflow agent

Own `src/workflow-agents.mjs`. Share readiness and selection between setup and workflow startup; a signed-out or missing optional agent must not block a ready one. For Codex and Claude, ready means credentials configured, not a successful provider authentication; expired/revoked credentials are not detected by status. This module does not start a chat, install a tool, change authentication, read credential files, or allocate a worktree. Gemini has no cheap authentication-status command: a successful `gemini --version` establishes installation and permits setup/startup; sign-in is checked when the chat starts. Antigravity CLI (`agy`) is ready when `agy models` lists models: it lists them only for a signed-in person and sends no model query; signed out, it exits 1 with a "sign in" line. No version is pinned. Its decisions use native noninteractive probes, with the caller's HOME, PATH, CODEX_HOME, CLAUDE_CONFIG_DIR and GEMINI_CLI_HOME unchanged; a named agents.json entry adds only its own env overrides. Try-page read-only capability checks are a separate policy.

Export module functions `chooseWorkflowAgent({codex,claude,gemini,agy,requested})`, `checkWorkflowAgents({cwd,env,requested},ports)`, `workflowAgentEntry(requested,{cwd,env})` and `reservedEnvMessage({name,env})`, and the constants `LOGIN_VARIABLES` and `SHELL_RESERVED_NAMES`. The pure chooser receives readiness states `ready`, `missing`, `signed_out` or `unavailable`; requested is absent, `codex`, `claude`, `gemini` or `agy`. Return `{ok,agent,message}`, with a selected agent and empty message on success, otherwise null agent and plain actionable guidance. Invalid states are unavailable; invalid requested names refuse without a probe. For compatibility, an omitted `gemini` or `agy` state on the pure chooser leaves that agent out of the candidate set and its guidance, unless it is explicitly requested. Native probing always supplies all four states.

| Choice | Outcome |
| --- | --- |
| Explicit agent | Use it only if ready; never silently switch to another agent. |
| No explicit agent, Codex ready | Select Codex, including when other agents are ready. |
| No explicit agent, Codex unavailable, Claude ready | Select Claude. |
| No explicit agent, Codex and Claude not ready, Gemini ready | Select Gemini. |
| No explicit agent, only Antigravity CLI ready | Select agy. |
| None ready | Refuse with installation/sign-in/status guidance for the states actually observed. |

All missing: say `Install Codex, Claude Code, Gemini CLI or Antigravity CLI first.` (naming only the candidates in the set) and provide the official install links (Gemini: https://geminicli.com/docs/get-started/installation/, Antigravity CLI: https://antigravity.google/docs/cli/). Otherwise give one actionable line for each unavailable candidate: missing means install that agent; signed_out means `Codex is not signed in. Run: codex login` or `Claude Code is not signed in. Run: claude auth login`; Gemini guidance uses `gemini` for sign-in and `gemini --version` for an unavailable probe; Antigravity CLI guidance uses `agy` for sign-in and `agy models` for an unavailable probe; unavailable means its sign-in could not be checked and gives its status command. Never display raw authentication stdout/stderr, user/account details, credentials or config paths. One ready candidate makes an unselected candidate's failure irrelevant.

`checkWorkflowAgents` uses an injectable async `ports.run(command,argv,options)` (default the existing native process runner). Check all candidates in parallel when no agent is requested, with the whole group bounded by one status-probe wait rather than two sequential waits; an explicit request checks only that candidate. Run only `codex login status`, `claude auth status`, `gemini --version` or `agy models`; do not run login/logout, interactive prompts, a model query, or unrelated tool commands. Use the supplied cwd/env, closed stdin, at most 16 KiB output and the native status-probe wait bound of 10 seconds. No version pin, HOME/config inference, credential lookup, cached readiness or fallback to another environment.

A native ENOENT counts as missing only with the process port's explicit executableMissing evidence. Otherwise it is unavailable, including a missing cwd, missing shebang interpreter or an uncertain injected error. For Gemini accept exit 0 with nonblank version stdout as installed; every other reply is unavailable. For agy, exit 0 with nonblank stdout is ready, exit 1 with a "sign in" line is signed_out, and every other reply is unavailable.

Gemini CLI serves only a paid Gemini API key, Vertex AI or Code Assist; free and Google One accounts use Antigravity CLI. When `checkWorkflowAgents` selects Gemini and none of `GEMINI_API_KEY`, `GOOGLE_API_KEY`, `GOOGLE_GENAI_USE_VERTEXAI` or `GOOGLE_GENAI_USE_GCA` is set in the caller environment, add `hint`: `With a free or Google One account, Gemini CLI does not run; use Antigravity CLI: --agent agy.` It is one line, does not change the selection and reads no files. Otherwise there is no `hint` field. Delegate Codex/Claude response interpretation to [the shared credential-status owner](agent-adapters.prompt.md#shared-credential-status-interpretation) parseAgentAuthStatus. Transport failures, interrupted/overlong responses and untyped status remain unavailable; wrapper banners cannot establish Claude readiness. Do not infer readiness from a config folder or another agent's result.

## Login variables

`LOGIN_VARIABLES` is the one list, per agent kind, of the environment variables that choose an agent's login or account. Every chat launch and resume in the [chat owner](workflow-chat.prompt.md#chat-login) uses it. It is a frozen object of frozen arrays:

| Kind | Login variables |
| --- | --- |
| `claude` | `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, `CLAUDE_CODE_OAUTH_TOKEN`, `ANTHROPIC_BASE_URL`, `CLAUDE_CODE_USE_BEDROCK`, `CLAUDE_CODE_USE_VERTEX` |
| `codex` | `OPENAI_API_KEY`, `CODEX_API_KEY`, `CODEX_ACCESS_TOKEN`, `OPENAI_FEDERATION_RULE_ID`, `OPENAI_IDENTITY_TOKEN_FILE`, `OPENAI_WORKLOAD_IDENTITY_CONTEXT`, `OPENAI_BASE_URL` |
| `gemini` | `GEMINI_API_KEY`, `GOOGLE_API_KEY`, `GOOGLE_GENAI_USE_VERTEXAI`, `GOOGLE_GENAI_USE_GCA`, `GOOGLE_APPLICATION_CREDENTIALS`, `GOOGLE_CLOUD_PROJECT` |
| `agy` | none: Antigravity CLI keeps its sign-in in the person's home |

The config-folder variable (`CODEX_HOME`, `CLAUDE_CONFIG_DIR`, `GEMINI_CLI_HOME`) is not in this list: the run saves it as `configDir`, and the chat owner sets or unsets it from that saved value. This module never reads, prints or stores a login value.

The Codex list covers API keys, an access token and workload identity login. A stale workload identity selection on the Herdr server must not choose the chat's account.

`ANTHROPIC_BASE_URL` and `OPENAI_BASE_URL` are in the list because the endpoint goes with the key: a stale endpoint from the Herdr server must never get the caller's key, and a caller without one gets the agent's default endpoint. The Gemini start check (`gemini --version`) does not check sign-in. So a caller without any Gemini login variable gives the chat none, and Gemini then uses only its own settings in its config folder; the free-account `hint` above appears for this case.

## Named agents.json entries

`--agent` names a built-in agent (`codex`, `claude`, `gemini`, `agy`) or the `name` of an entry in the person's `~/.config/pdd/agents.json` ([named local agents](agent-config.prompt.md)). `workflowAgentEntry(requested,{cwd,env})` decides which, without a probe:

| `requested` | Result |
| --- | --- |
| absent, or a built-in name | `{ok:true, agent:requested, definition:null}`; agents.json is not read, so a built-in name works exactly as before, also when an entry has that name |
| the name of an enabled default entry (`Codex`, `Claude`, `Gemini`) | `{ok:true, agent:<its kind>, definition:null}`: it is the built-in agent |
| the name of a custom entry | `{ok:true, agent:<its kind>, definition:{name,kind,command,env}}`, the loaded record with `~` already expanded |
| the name of a custom entry whose env sets a [shell-reserved name](#shell-reserved-names) | `{ok:false, agent:null, message}` with the `reservedEnvMessage` text |
| any other text | `{ok:false, agent:null, message}`: `Unknown agent "<text>". Choose --agent codex, --agent claude, --agent gemini or --agent agy, or a name from ~/.config/pdd/agents.json: "<name>", "<name>".` with every custom entry name in file order, or `… or --agent agy. ~/.config/pdd/agents.json has no agent with that name.` when it has none |
| any text while agents.json is invalid | `{ok:false, agent:null, message}`: the loader's plain error, then `Fix ~/.config/pdd/agents.json, or choose --agent codex, --agent claude, --agent gemini or --agent agy.` |

The requested text and the names are shown as JSON strings, so a control character stays visible and harmless. The message never shows a command or an env value.

`checkWorkflowAgents` with a requested entry name resolves it first. A refusal returns that refusal without a probe. For a custom entry it runs the same status command as for its kind, but with the entry's `command` as the program and the caller environment plus the entry's `env` overrides: the same program and environment that the chat starts. It returns the chooser result for that kind plus `name` (the entry name) on success. A not-ready entry gets one line: `<agent display name> (agents.json entry "<name>") is not signed in. Sign in with that entry's command, then run the command again.`, `… is not installed or its command was not found. Fix the command in ~/.config/pdd/agents.json.` or `… sign-in could not be checked. Run that entry's command with <status arguments>.`; it never shows the command text. A built-in request keeps its exact earlier probes, guidance and result, with no `name` field.

<a id="shell-reserved-names"></a>
## Shell-reserved names

A chat gets the entry's env values from a child `sh` that runs `export NAME='value'` ([chat login](workflow-chat.prompt.md#chat-login)). Some names belong to the shell: it refuses to set them (the `sh` then stops, and the agent does not start), or it sets its own value, so the entry's value never reaches the agent. `SHELL_RESERVED_NAMES` is the frozen list of these names, found with bash, dash, BusyBox ash, zsh and ksh each run as `sh`, on macOS and Linux:

`BASHOPTS`, `BASHPID`, `BASH_ALIASES`, `BASH_ARGC`, `BASH_ARGV`, `BASH_CMDS`, `BASH_COMMAND`, `BASH_LINENO`, `BASH_SOURCE`, `BASH_SUBSHELL`, `BASH_VERSINFO`, `DIRSTACK`, `EGID`, `EPOCHREALTIME`, `EPOCHSECONDS`, `EUID`, `FUNCNAME`, `GID`, `GROUPS`, `HISTCMD`, `KSH_VERSION`, `LINENO`, `OPTIND`, `PIPESTATUS`, `PPID`, `RANDOM`, `SECONDS`, `SHELLOPTS`, `SHLVL`, `SRANDOM`, `TTYIDLE`, `UID`, `ZSH_EVAL_CONTEXT`, `ZSH_SUBSHELL`, `_`, `signals`.

Number settings that a person may choose (for example `COLUMNS`, `LINES`, `HISTSIZE`, `TMOUT`) are not in the list: zsh keeps a number value as it is.

`reservedEnvMessage({name, env})` returns null when no env name of the entry is in the list. Otherwise it returns one line, with the names in env order: `The agents.json entry "<name>" sets names in env that the shell controls: UID, PPID. pdd cannot give them to the chat. Remove them from that entry's env, then run the command again.` The entry name is a JSON string; the line never shows a command or an env value. `workflowAgentEntry` refuses such an entry at start, and the chat owner refuses it again at each launch.

## Dependencies

- Load the [Prompting guide](../../docs/prompting-guide.md) for authoring and generation.
- [Named local agents](agent-config.prompt.md) owns `loadAgentDefinitions` and the agents.json format, validation and `~` expansion; this module only selects an entry by name.
- [Agent adapters](agent-adapters.prompt.md) owns the reusable `runAgentProcess` native process boundary, including closed input, process cleanup, bounded output, executableMissing evidence and the shared parseAgentAuthStatus credential-status rules. This module supplies only status commands, the caller environment and the probe bounds; it does not use Try discovery or invoke the model adapter.
- The [CLI](pdd-cli.prompt.md#setup-and-workflow-admission) and [runner](workflow-runner.prompt.md#commands) own setup/startup dispatch and all subsequent effects. A refused readiness result must not be interpreted as a started workflow. They do not infer readiness themselves.
- Navigation only: [Claude Code CLI](https://code.claude.com/docs/en/cli-reference). Commands and accepted readiness facts are specified above so generation does not depend on a live documentation fetch.

<details><summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "59c0ad4e8151d6fa433a5e4a22929325e007e093f4ee995376adab057c3d85d4",
  "entries": [
    {
      "operation": "chooseWorkflowAgent",
      "input_schema": {
        "type": "object",
        "properties": {
          "codex": {
            "type": "string",
            "enum": [
              "ready",
              "missing",
              "signed_out",
              "unavailable"
            ]
          },
          "claude": {
            "type": "string",
            "enum": [
              "ready",
              "missing",
              "signed_out",
              "unavailable"
            ]
          },
          "gemini": {
            "type": "string",
            "enum": [
              "ready",
              "missing",
              "signed_out",
              "unavailable"
            ]
          },
          "agy": {
            "type": "string",
            "enum": [
              "ready",
              "missing",
              "signed_out",
              "unavailable"
            ]
          },
          "requested": {
            "type": "string",
            "enum": [
              "codex",
              "claude",
              "gemini",
              "agy"
            ]
          }
        },
        "required": [
          "codex",
          "claude"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "ok": {
            "type": "boolean"
          },
          "agent": {
            "oneOf": [
              {
                "type": "string",
                "enum": [
                  "codex",
                  "claude",
                  "gemini",
                  "agy"
                ]
              },
              {
                "type": "null"
              }
            ]
          },
          "message": {
            "type": "string"
          }
        },
        "required": [
          "ok",
          "agent",
          "message"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 1,
    "max_model_calls": 1
  },
  "conventions": []
}
```
</details>
