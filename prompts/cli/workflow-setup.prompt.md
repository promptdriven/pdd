# Run setup only with a ready workflow agent

Own `src/workflow-setup.mjs`; export module function `setupWithWorkflowAgent({cwd,env},ports)`. This is the setup admission adapter, independent of the shared CLI's command routing. It does not install skills, write agent files or start chats itself. The caller supplies its existing setup action; the shared CLI owner wires that action to this adapter separately.

First validate that ports.setup is a function; otherwise print a safe missing-action recovery instruction and return 1 without any status process. Then use [workflow readiness](workflow-agents.prompt.md) `checkWorkflowAgents({cwd,env},ports)`, with the exact caller environment and its injectable native status process. A false result prints only the readiness owner's safe actionable message to ports.stderr and returns 1. An unavailable candidate is handled by the readiness owner’s safe status-command guidance. If the readiness call itself unexpectedly throws, print a generic status-command recovery instruction and return 1. Neither case may call the setup action. Never print raw exception/authentication details.

With a ready selection, print its optional one-line `hint` to ports.stderr, then call `ports.setup({agent,cwd,env})` once and return its integer exit status unchanged. A ready optional alternative is sufficient; setup itself does not require a particular agent. The existing skills/project/MCP actions and consent policy remain with their owners. The adapter adds no consent for those actions and never performs login, logout, installation, model calls or workflow allocation. Missing/invalid setup callbacks or invalid replies fail finitely with exit 1; never retry an action that threw or returned a bad result because it may already have written configuration.

## Dependencies

- Load the [Prompting guide](../../docs/prompting-guide.md) for authoring/generation.
- Load [workflow agent readiness](workflow-agents.prompt.md) for generation/testing/runtime admission policy. Ports.run is its native status boundary; this adapter does not infer sign-in from files or parse status output.
- [Skills install](skills-install.prompt.md), [project setup](project-setup.prompt.md), and [agent MCP setup](agent-mcp-setup.prompt.md) retain their existing setup behavior. The caller's supplied setup action owns their execution.
- The [CLI](pdd-cli.prompt.md) owns public dispatch. Adding this adapter does not by itself change pdd setup; the pending shared-file wiring must be integrated before claiming the public command fixed.

- In Runtime checks, `readiness.checkWorkflowAgents({cwd, env})` supplies `{ok, agent, hint, message}`, `setup.setup({agent, cwd, env})` executes the caller's setup callback and returns `{exitCode}`, and `stderr.write({text})` records stderr lines. An empty `cwd` fails with `invalid_setup_input` before any port call; when `hasSetup` is `false`, `setupWithWorkflowAgent` prints the missing-action recovery instruction to `stderr.write` and returns `{exitCode: 1}` without calling `readiness.checkWorkflowAgents`. Actual status processes, interactive consent, skill copies and configuration writes stay in `test/workflow-setup.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "59338a1229aa0ab7e814187c7453b2ef2faff7747cce43051ef984a1db5eaaf5",
  "entries": [
    {
      "operation": "setupWithWorkflowAgent",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "object",
            "properties": {
              "HOME": {
                "type": "string"
              },
              "PDD_AGENT": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "hasSetup": {
            "type": "boolean"
          }
        },
        "required": [
          "cwd",
          "env"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exitCode": {
            "type": "integer"
          }
        },
        "required": [
          "exitCode"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_setup_input"
      ],
      "resource_operations": [
        "readiness.checkWorkflowAgents",
        "setup.setup",
        "stderr.write"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "readiness",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "checkWorkflowAgents",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PDD_AGENT": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "cwd",
              "env"
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
                    "type": "object",
                    "properties": {
                      "agent": {
                        "type": "string"
                      },
                      "command": {
                        "type": "string"
                      },
                      "status": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "agent",
                      "command",
                      "status"
                    ],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "hint": {
                "type": "string"
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "ok",
              "agent",
              "hint",
              "message"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "setup",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "setup",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "agent": {
                "type": "object",
                "properties": {
                  "agent": {
                    "type": "string"
                  },
                  "command": {
                    "type": "string"
                  },
                  "status": {
                    "type": "string"
                  }
                },
                "required": [
                  "agent",
                  "command",
                  "status"
                ],
                "additionalProperties": false
              },
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PDD_AGENT": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "agent",
              "cwd",
              "env"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              }
            },
            "required": [
              "exitCode"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "stderr",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "text": {
                "type": "string"
              }
            },
            "required": [
              "text"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 24,
    "max_model_calls": 10
  },
  "conventions": []
}
```
</details>
