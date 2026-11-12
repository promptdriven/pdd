# Autopilot first-start doctor

Own `src/autopilot-doctor.mjs`. Export asynchronous `runAutopilotDoctor(input,
ports = {})`. Input carries cwd, packageRoot and env, and an optional saved profile binding
(agent id/kind, home, definitionHome, configHome). Preserve existing launcher
behavior except the authorized required preflight before startup effects.
The doctor is read-only: no GitHub writes, agent generation, interpreter jobs,
state files, timer changes, workspace allocation, cleanup or approvals.

The core engine is the only Autopilot engine. Its jobs run headless, so doctor
has no Herdr check and makes no Herdr call. The launcher can also pass `engine`,
`coordinatorPaneId` and a `coordinatorHealth` port. Doctor ignores them.

Return {exitCode, message, checks}. Checks are ordered records with exactly id,
status (pass, warn, fail), detail and fix. Every record has a fix, also a pass
record. Exit 1 only for missing or signed-out
agent sign-in; otherwise exit 0. This is the only new refusal allowed before
native start. Every other doctor finding is WARN with a fix command, including
a different pdd on PATH, read-only repository permission and disabled merge
methods, in both observe and auto mode. Preserve native start admission,
cleanup, parking and recovery decisions. Start displays advisory lines and
continues to its native guards; doctor findings must not add other refusals.
Message has one line per record. A pass line is `PASS id: detail`: it shows no
fix. A warn or fail line is `STATUS id: detail; fix: command`.
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

Printed commands must target that invocation environment. Compare it with the
caller environment for HOME, PATH, CODEX_HOME, CLAUDE_CONFIG_DIR, GEMINI_CLI_HOME
and each override name of the selected definition. Bind only the names that
differ: an explicit unset (`-u NAME`) when the caller has NAME and the invocation
environment does not, and `NAME=value` when the value differs. Such a fix is
`env BINDINGS /bin/sh -c 'COMMAND'`. When no name differs, the fix is the plain
command. Non-secret values are literal and safely quoted;
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
- Git identity (`git-identity`): Autopilot jobs commit, so they need a name and an
  email. Read the effective `git config user.name` and `git config user.email` in
  the repository folder with the invocation environment. In that environment, a
  nonblank GIT_AUTHOR_NAME and GIT_COMMITTER_NAME also give the name, and a nonblank
  GIT_AUTHOR_EMAIL and GIT_COMMITTER_EMAIL (or EMAIL) also give the email, as Git
  reads them. A missing value warns: `Git user.name and user.email are needed for
  Autopilot commits; missing: NAMES`, where NAMES is `user.name`, `user.email` or
  both. The fix sets only the missing values, joined with ` && `:
  `git config --global user.name "Your Name"` and
  `git config --global user.email "you@example.com"`. With both values, pass with
  `Git user.name and user.email are set for Autopilot commits` and the fix
  `git config user.name && git config user.email`.
- Choose a signed-in configured agent using the launcher's normal provider order
  and invocation environment. Probe only Codex login status or Claude auth status
  --json (preserve supported agy/Gemini launcher selection through its read-only readiness/credential ports). When sign-in is missing or signed out, fail with the installed agent's sign-in
  command. A configuration read error is advisory; it does not establish missing
  sign-in and must not create a failing agent check. Missing CLIs name their install command. Read Codex limits using its
  read-only account port. Limited and unknown are warnings. For Claude,
  unsupported read-only usage evidence is warning with `claude` and /usage advice;
  no generation call to discover allowance, and no credit/reset advice.
- Setup: require a complete PDD block in AGENTS.md or CLAUDE.md, all seven skill
  entrypoints in one selected provider's supported project/user skill root,
  and valid pdd.json autopilot mode/trust. Off warns; native start owns mode admission. Describe observe versus auto
  authority, owner/write-access trust even with [], explicit trusted users and
  strict approvals in plain words. Never change mode or trust.
- GitHub settings (`settings-github`): Autopilot job worktrees and other machines
  start from GitHub, so they read `pdd.json` of the default branch there. Read it
  with `gh api repos/REPO/contents/pdd.json?ref=BRANCH` (REPO and BRANCH from the
  `gh repo view` read above; the branch is URL-encoded) and decode its base64
  content. A gh reply with `(HTTP 404)` means that GitHub has no file. The settings
  differ as [Autopilot settings on GitHub](autopilot-github.prompt.md#publish)
  defines: the effective mode or the trust names, ignoring case and order. SETTINGS
  is that prompt's `MODE, trust NAMES` form. The first matching row decides:

  | Observation | Status | Detail | Fix |
  |---|---|---|---|
  | No REPO or BRANCH, a failed read, or a file that is not a base64 JSON object | warn | `Autopilot settings on GitHub are unproved; doctor could not read pdd.json of the default branch` | `gh auth login && ` plus the read command, or `gh auth login` without REPO or BRANCH |
  | This checkout has a `pdd.json` that is not a JSON object | warn | `pdd.json in this checkout is not a JSON object; the GitHub comparison is unproved` | `vi pdd.json` |
  | No file on GitHub and none in this checkout | warn | `pdd.json is missing in this checkout and on GitHub (BRANCH)` | `pdd setup` |
  | No file on GitHub | warn | `pdd.json is only in this checkout; GitHub (BRANCH) has none, so other machines and Autopilot job worktrees do not see it` | `git add pdd.json && git commit -m "Add PDD settings" && git push`, plus ` # or pdd autopilot MODE` when the local mode is observe or auto |
  | No file in this checkout | warn | `pdd.json is only on GitHub (BRANCH): SETTINGS; this checkout has none` | `git fetch origin && git checkout origin/BRANCH -- pdd.json` |
  | The settings differ | warn | `GitHub: SETTINGS; this checkout: SETTINGS; Autopilot jobs use the GitHub copy` | The publish commands of that prompt's Check, joined with ` && `: `pdd autopilot MODE` (the local mode) when the modes differ, `pdd autopilot trust NAMES` and `pdd autopilot untrust NAME` |
  | The same settings | pass | `GitHub (BRANCH) has the same Autopilot settings: SETTINGS` | the read command |

  The read command is `gh api 'repos/REPO/contents/pdd.json?ref=BRANCH' -H
  'Accept: application/vnd.github.raw'`. A trust name or `origin/BRANCH` in a fix
  is shell-quoted unless it has only letters, digits and `_ . @ / -`. Doctor
  makes no GitHub write here: only the printed fix publishes.
- Enumerate tracked *.prompt.md and report draft/missing interfaces as advisory
  paths that may need approval on first check. Malformed or unreadable prompts
  warn. Never approve them or block doctor solely for drafts.
- Read interpreter access through the [Runtime seam](runtime-seam.prompt.md) `health` check (`checkRuntimeHealth`)
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
- [PDD to Runtime seam](runtime-seam.prompt.md) and [Runtime client](runtime-client.prompt.md#free-interpreter-health-check): required `health` classification and `runtimeOrigin` address rules.
- [Autopilot settings on GitHub](autopilot-github.prompt.md): owns when two
  Autopilot settings differ, the `MODE, trust NAMES` form and the publish commands.
  Doctor reads GitHub with its own read-only run port, not with that module's ports.

All program, file, network, environment/platform/version/uid and account reads
have injected ports. Native defaults are adapter bindings only. Files provides
readFileSync, realpathSync, accessSync and statSync; run accepts executable,
argv and cwd/env options and returns code/stdout/stderr. agentDefinitions,
selectAgent, codexLimits, runtimeHealth, fetch and spawn are independently
replaceable ports. onSelection observes the resolved selection before checks;
the launcher uses its env and agent for startup after a passing report.
Do not use a GitHub ledger that writes reads to disk. Do not mutate arrays returned by definition ports.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "partial",
  "status": "draft",
  "prose_sha256": "672f4dc5010bf15ab643f59366e903c35ddab435ea5caec73872fa197740d404",
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
