# Autopilot first-start doctor

Own `src/autopilot-doctor.mjs`. Export asynchronous `runAutopilotDoctor(input,
ports = {})`. Input carries cwd, packageRoot and env. Preserve existing launcher
behavior except the authorized required preflight before startup effects.
The doctor is read-only: no GitHub writes, agent generation, interpreter jobs,
state files, timer changes, workspace allocation, cleanup or approvals.

Return {exitCode, message, checks}. Checks are ordered records with exactly id,
status (pass, warn, fail), detail and fix. Exit 1 if any required check fails,
else 0. Message has one line per record: STATUS id: detail; fix: command.
Collapse control characters and newlines in details. Never echo auth payloads,
tokens or provider diagnostics. Each fix is a concrete shell command, safely
quoted for paths, with a diagnostic command for successful checks or conditions
that need inspection. Report unavailable evidence, never invent a successful read.

Check these boundaries in order and continue after failures:
- PATH: first executable pdd resolves to packageRoot/bin/pdd.mjs and its help
  advertises autopilot. A different install is required failure even at the same
  version; include its path and safe version. Fix with an absolute Node plus
  this CLI doctor command, so source checkouts work too.
- Node >=22.20.0; Git present; Git checkout and GitHub origin; gh signed in;
  repo viewerPermission is ADMIN, MAINTAIN or WRITE and at least one merge method
  is enabled. Missing tools, auth or write permission are failures. Read effective
  rules for the default branch separately. Unreadable rules warn; list rule types
  and say required reviews/checks still apply. Do not claim merge eligibility.
- Choose a signed-in configured agent using the launcher's normal provider order
  and invocation environment. Probe only Codex login status or Claude auth status
  --json (preserve supported agy/Gemini launcher selection through its read-only readiness/credential ports). Without a selected account fail with the installed agent's sign-in
  command. Missing CLIs name their install command. Read Codex limits using its
  read-only account port. Limited is failure, unknown is warning. For Claude,
  unsupported read-only usage evidence is warning with `claude` and /usage advice;
  no generation call to discover allowance, and no credit/reset advice.
- Herdr installed. Read the workflow session `pdd` server status and pane list without starting a server, matching the shared workflow pane budget.
  A stopped server has zero panes. Apply PDD_HERDR_PANE_BUDGET (default 56,
  0 unlimited); insufficient room for one coordinator fails, invalid budget or
  unreadable inventory fails. Recommend the native tidy command for capacity.
- Setup: require a complete PDD block in AGENTS.md or CLAUDE.md, all ten skill
  entrypoints in one selected provider's supported project/user skill root,
  and valid pdd.json autopilot mode/trust. Off fails. Describe observe versus auto
  authority, owner/write-access trust even with [], explicit trusted users and
  strict approvals in plain words. Never change mode or trust.
- Enumerate tracked *.prompt.md and report draft/missing interfaces as advisory
  paths that may need approval on first check. Malformed or unreadable prompts
  warn. Never approve them or block doctor solely for drafts.
- Read interpreter access with gh auth token and authenticated GET /v1/capacity
  at the shared runtime origin. No upload or job. Require HTTP 200 JSON to prove
  access; missing auth, denial, maintenance, unsupported endpoint or unreachable
  access fail with gh auth login, the platform browser sign-up command or a doctor
  retry as appropriate. No auth body or token appears in the report.
- Linux requires a readable systemd user session; lingering is advisory for logout
  persistence and names loginctl enable-linger. macOS requires a readable launchctl
  user domain; read pmset and warn when sleep can pause work, with caffeinate -i.
  Other platforms fail. All checks have exact commands for diagnosis or repair.

## Dependencies

- [Agent adapters](agent-adapters.prompt.md): sign-in parsers and non-model process port.
- [Agent config](agent-config.prompt.md): provider definitions and profile environment.
- [Workflow worktree](workflow-worktree.prompt.md): canonical GitHub origin normalization.
- [Workflow agents](workflow-agents.prompt.md): read-only agy readiness.
- [Codex limits](codex-limits.prompt.md): read-only account usage states.
- [Runtime client](runtime-client.prompt.md): runtimeOrigin is the one address setting.

All program, file, network, environment/platform/version/uid and account reads
have injected ports. Native defaults are adapter bindings only. Files provides
readFileSync, realpathSync, accessSync and statSync; run accepts executable,
argv and cwd/env options and returns code/stdout/stderr. agentDefinitions,
selectAgent, codexLimits, runtimeHealth, fetch and spawn are independently
replaceable ports. Do not use a GitHub ledger that writes reads to disk. Do not mutate arrays returned by definition ports.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "partial",
  "status": "draft",
  "prose_sha256": "",
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
