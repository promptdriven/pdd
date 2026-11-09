# Run setup only with a ready workflow agent

Own `src/workflow-setup.mjs`; export module function `setupWithWorkflowAgent({cwd,env},ports)`. This is the setup admission adapter, independent of the shared CLI's command routing. It does not install skills, write agent files or start chats itself. The caller supplies its existing setup action; the shared CLI owner wires that action to this adapter separately.

First validate that ports.setup is a function; otherwise print a safe missing-action recovery instruction and return 1 without any status process. Then use [workflow readiness](workflow-agents.prompt.md) `checkWorkflowAgents({cwd,env},ports)`, with the exact caller environment and its injectable native status process. A false result prints only the readiness owner's safe actionable message to ports.stderr and returns 1. An unavailable candidate is handled by the readiness owner’s safe status-command guidance. If the readiness call itself unexpectedly throws, print a generic status-command recovery instruction and return 1. Neither case may call the setup action. Never print raw exception/authentication details.

With a ready selection, print its optional one-line `hint` to ports.stderr, then call `ports.setup({agent,cwd,env})` once and return its integer exit status unchanged. A ready optional alternative is sufficient; setup itself does not require a particular agent. The existing skills/project/MCP actions and consent policy remain with their owners. The adapter adds no consent for those actions and never performs login, logout, installation, model calls or workflow allocation. Missing/invalid setup callbacks or invalid replies fail finitely with exit 1; never retry an action that threw or returned a bad result because it may already have written configuration.

## Dependencies

- Load the [Prompting guide](../../docs/prompting-guide.md) for authoring/generation.
- Load [workflow agent readiness](workflow-agents.prompt.md) for generation/testing/runtime admission policy. Ports.run is its native status boundary; this adapter does not infer sign-in from files or parse status output.
- [Skills install](skills-install.prompt.md), [project setup](project-setup.prompt.md), and [agent MCP setup](agent-mcp-setup.prompt.md) retain their existing setup behavior. The caller's supplied setup action owns their execution.
- The [CLI](pdd-cli.prompt.md) owns public dispatch. Adding this adapter does not by itself change pdd setup; the pending shared-file wiring must be integrated before claiming the public command fixed.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

readiness.checkWorkflowAgents and setup.setup bind the existing readiness and ports.setup callbacks; stderr binds the actual output stream. Missing-action tests omit the setup binding. Supplied replies cover ordering and exactly-once decisions only. Actual status processes, consent, installs and configuration writes remain native. Native evidence owners: test/workflow-setup.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "d731c1122403b57d003af0144fc99f5d217b22d2ddef548a7626bbad19e1d7c4",
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
            "type": "string",
            "description": "JSON text encoding of the caller environment. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
      "errors": [],
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
                "type": "string",
                "description": "JSON text encoding of the exact caller environment. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
              "value": {
                "type": "string",
                "description": "JSON text encoding of the readiness reply including ready agent or safe message. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "value"
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
                "type": "string",
                "description": "JSON text encoding of the ready selection. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              },
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "string",
                "description": "JSON text encoding of the exact caller environment. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
    "max_steps": 64,
    "max_model_calls": 16
  },
  "conventions": [],
  "kind": "partial"
}
```
</details>
