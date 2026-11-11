# Autopilot first-start doctor

Own `src/autopilot-doctor.mjs`. Export asynchronous `runAutopilotDoctor(input,
ports = {})`. Input carries cwd, packageRoot and env, and an optional saved profile binding
(agent id/kind, home, definitionHome, configHome), plus optional coordinatorPaneId. Preserve existing launcher
behavior except the authorized required preflight before startup effects.
The doctor is read-only: no GitHub writes, agent generation, interpreter jobs,
state files, timer changes, workspace allocation, cleanup or approvals.

Return {exitCode, message, checks}. Checks are ordered records with exactly id,
status (pass, warn, fail), detail and fix. Exit 1 only for missing or signed-out
agent sign-in; otherwise exit 0. This is the only new refusal allowed before
native start. Every other doctor finding is WARN with a fix command, including
a different pdd on PATH, read-only repository permission and disabled merge
methods, in both observe and auto mode. Preserve native start admission,
cleanup, parking and recovery decisions. Start displays advisory lines and
continues to its native guards; doctor findings must not add other refusals.
Message has one line per record: STATUS id: detail; fix: command.
Collapse control characters and newlines in details. Never echo auth payloads,
tokens or provider diagnostics. Each fix is a concrete shell command, safely
quoted for paths, with a diagnostic command for successful checks or conditions
that need inspection. Report unavailable evidence, never invent a successful read.

Resolve the selected definition before prerequisite probes. Load definitions from
saved definitionHome when a profile is supplied, restrict selection to its agent
id/kind, and preserve saved HOME and provider config home after definition overrides.
Otherwise merge the selected definition's env over the caller environment. Use
this invocation environment for every prerequisite, including PATH, GitHub,
provider sign-in, usage, skills, interpreter and scheduling. Claude user skills
live under CLAUDE_CONFIG_DIR/skills when set; HOME overrides select user roots.
Keep the caller environment unchanged. An agents.json read or parse failure gets
its own advisory agent-config line with the actual file path and an editor repair
command; never echo raw errors or configuration values.

Export resolveAutopilotAgent(input, ports = {}) for the launcher's same selection
policy. Return agent (definition or null), preferred (definition or undefined),
installed (probed definitions), env (effective invocation environment), and
configurationError (caught load error or null). Program/file/config selection ports
match the doctor. A saved binding wins over conflicting definition profile values.

Printed commands must target that invocation environment. Preserve safe PATH,
HOME, CODEX_HOME, CLAUDE_CONFIG_DIR and GEMINI_CLI_HOME bindings and explicit unsets
for absent provider directories. Include other non-secret definition overrides as literal bindings;
credential-named bindings and URLs with credentials, query or fragment use shell
variable references, never literal secret values.
Report no raw provider/configuration error or auth payload. A failed inspection
must also name the repair action (enable a merge method, edit config, restore the
user service/session, or sign in); a status command alone is insufficient.

Check these boundaries in order and continue after failures:
- PATH: first executable pdd resolves to packageRoot/bin/pdd.mjs and its help
  advertises autopilot. A different install warns even at the same
  version; include its path and safe version. Fix with an absolute Node plus
  this CLI doctor command, so source checkouts work too.
- Node >=22.20.0; Git present; Git checkout and GitHub origin; gh signed in;
  repo viewerPermission is ADMIN, MAINTAIN or WRITE and at least one merge method
  is enabled. Missing tools, gh auth or write permission warn. Read effective
  rules for the default branch separately. Unreadable rules warn; list rule types
  and say required reviews/checks still apply. Do not claim merge eligibility.
- Choose a signed-in configured agent using the launcher's normal provider order
  and invocation environment. Probe only Codex login status or Claude auth status
  --json (preserve supported agy/Gemini launcher selection through its read-only readiness/credential ports). When sign-in is missing or signed out, fail with the installed agent's sign-in
  command. A configuration read error is advisory; it does not establish missing
  sign-in and must not create a failing agent check. Missing CLIs name their install command. Read Codex limits using its
  read-only account port. Limited and unknown are warnings. For Claude,
  unsupported read-only usage evidence is warning with `claude` and /usage advice;
  no generation call to discover allowance, and no credit/reset advice.
- With the core engine (the input's `engine`, which a machine start saved, else
  `autopilot.engine: "core"` in the checked repository's `pdd.json`), jobs run
  headless: report `PASS herdr: Not needed: autopilot.engine is core, so jobs run
  headless without Herdr`, run no Herdr command and add no `herdr-room` check.
  Otherwise:
- Herdr installed. Read the workflow session `pdd` server status and pane list without starting a server, matching the shared workflow pane budget.
  A stopped server has zero panes. Apply PDD_HERDR_PANE_BUDGET (default 56,
  0 unlimited), using the workflow owner's ensurePaneBudget with cleanup disabled,
  rather than a second parser or inventory policy. Only charge the one pane that
  openWorkspace actually allocates on a fresh start. For a saved coordinator, use
  the launcher's coordinatorHealth in session `pdd-autopilot`; never search for
  that pane in `pdd`. A verified coordinator needs no allocation or workflow room
  read. An unavailable or mismatched saved target warns and defers to the existing
  guarded start recovery; preflight must not refuse a start that native start
  admits. Saved custody and pending delivery also defer allocation to their guards.
  Insufficient room, invalid budget and unreadable inventory warn and defer to
  native start. This includes a finished workflow shell after its chat has closed:
  preflight does not need to predict which panes native cleanup can reclaim.
  Recommend the native tidy command for capacity, or unset an invalid budget.
- Setup: require a complete PDD block in AGENTS.md or CLAUDE.md, all ten skill
  entrypoints in one selected provider's supported project/user skill root,
  and valid pdd.json autopilot mode/trust. Off warns; native start owns mode admission. Describe observe versus auto
  authority, owner/write-access trust even with [], explicit trusted users and
  strict approvals in plain words. Never change mode or trust.
- Enumerate tracked *.prompt.md and report draft/missing interfaces as advisory
  paths that may need approval on first check. Malformed or unreadable prompts
  warn. Never approve them or block doctor solely for drafts.
- Read interpreter access through the runtime client's existing checkRuntimeHealth
  with the selected environment and injected gh/fetch/clock ports. No upload or job.
  Preserve its health rules, including a JSON 404 from an interpreter without the
  optional capacity endpoint. Missing auth, denial, maintenance or unreachable
  access warn with gh auth login, the platform browser sign-up command or a doctor
  retry as appropriate. Validate the origin even with an injected health port. An
  invalid PDD_RUNTIME_URL names that setting and advises an HTTPS origin or unsetting
  it to use the default, with an executable unset-and-retry command. No auth body
  or token appears in the report.
- Linux checks for a readable systemd user session; lingering is advisory for logout
  persistence and names loginctl enable-linger. macOS checks for a readable launchctl
  user domain; read pmset and warn when sleep can pause work, with caffeinate -i.
  Other platforms warn. All checks have exact commands for diagnosis or repair.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): register invocation secrets and
  gh/Gemini credentials read here in the in-memory value inventory.

- [Agent adapters](agent-adapters.prompt.md): sign-in parsers and non-model process port.
- [Agent config](agent-config.prompt.md): provider definitions and profile environment.
- [Workflow worktree](workflow-worktree.prompt.md): canonical GitHub origin normalization.
- [Workflow agents](workflow-agents.prompt.md): read-only agy readiness.
- [Codex limits](codex-limits.prompt.md): read-only account usage states.
- [Runtime client](runtime-client.prompt.md#free-interpreter-health-check): required health classification and runtimeOrigin address rules.
- [Workflow chat](workflow-chat.prompt.md): required ensurePaneBudget admission and pane inventory rules; doctor disables all cleanup.

All program, file, network, environment/platform/version/uid and account reads
have injected ports. Native defaults are adapter bindings only. Files provides
readFileSync, realpathSync, accessSync and statSync; run accepts executable,
argv and cwd/env options and returns code/stdout/stderr. agentDefinitions,
selectAgent, codexLimits, coordinatorHealth, runtimeHealth, fetch and spawn are independently
replaceable ports. onSelection observes the resolved selection before checks;
the launcher uses its env and agent for startup after a passing report.
coordinatorHealth({env}) returns the launcher's {state, reason?} observation:
working, starting, idle, blocked, done, or unavailable with a reason. Unknown
or failed observations are advisory and leave recovery to start.
Do not use a GitHub ledger that writes reads to disk. Do not mutate arrays returned by definition ports.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "partial",
  "status": "approved",
  "prose_sha256": "18dae0f1a37855d569abe401be94c190e22b505c46127437f79e3ef7f04040fd",
  "entries": [
    {
      "operation": "runAutopilotDoctor",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "packageRoot": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "packageRoot"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exitCode": {
            "type": "integer",
            "enum": [
              0,
              1
            ]
          },
          "message": {
            "type": "string"
          },
          "checks": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "status": {
                  "type": "string",
                  "enum": [
                    "pass",
                    "warn",
                    "fail"
                  ]
                },
                "detail": {
                  "type": "string"
                },
                "fix": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "status",
                "detail",
                "fix"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "exitCode",
          "message",
          "checks"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "programs",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "run",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "command": {
                "type": "string"
              },
              "args": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "command",
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "code": {
                "type": "integer"
              },
              "stdout": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [
              "code",
              "stdout",
              "stderr"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "files",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readFileSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "found": {
                "type": "boolean"
              },
              "text": {
                "type": "string"
              }
            },
            "required": [
              "found",
              "text"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "realpathSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "found": {
                "type": "boolean"
              },
              "path": {
                "type": "string"
              }
            },
            "required": [
              "found",
              "path"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "accessSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "executable": {
                "type": "boolean"
              }
            },
            "required": [
              "executable"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "statSync",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "isFile": {
                "type": "boolean"
              }
            },
            "required": [
              "isFile"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 30,
    "max_model_calls": 12
  },
  "conventions": [
    "The partial interface declares the public report and local program/file observations. Provider definition, account usage, native environment and fetch bindings remain native ports; a full interpreter scenario is not supplied.",
    "Native file operations use strings, stat objects and exceptions. Resource transport wraps these as found/text, found/path, executable and isFile. Missing text/path is the empty string when found is false.",
    "Program environment and cwd are supplied by the invocation and selected agent definition; raw auth responses are never public output."
  ]
}
```

</details>
