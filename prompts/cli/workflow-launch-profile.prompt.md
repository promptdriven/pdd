# Run chat launch profiles

Own `src/workflow-launch-profile.mjs`. A launch profile selects settings for the
next chat without changing the person's account configuration. Preserve existing
agent kind, account isolation, full-access and agents.json login behavior.

`launchProfile(run, chat?)` returns a fresh profile with exactly `agent`,
`configDir` (folder or null), `model` (string or null), `herdrAgentName` (name
prefix), and `codexThreads` (integer or null). Prefer the chat's saved profile,
else the run's profile. A legacy chat without a snapshot uses its own agent and
configDir, with unset model and threads. A legacy run uses its saved fields.
Unset model and threads leave native defaults in effect. Default name prefix is
`pdd-` plus the first 12 hex SHA256 characters of repository and run identity.
`chatAgentName(profile, area, run)` appends `-` and the first six hex SHA256
characters of repository, run identity and area. Thus peer areas and independent runs have different names, while a
replacement of one area's closed chat keeps its name.

`selectLaunchProfile({run, configDir, model, herdrAgentName, codexThreads}, ports)`
merges explicitly supplied values into the run profile. Model must be a nonempty
trimmed string without controls or a leading dash. Name prefix must match
`[a-z][a-z0-9_-]{0,24}`. A requested Codex thread limit is a whole decimal number
from 4 through 8; reject it for other agents. Malformed options throw
`invalid_launch_profile` before effects. Omitted values retain saved settings.

When a Codex thread limit is selected, read only that account's `config.toml`
through `ports.profileFs` (default node:fs), using the expanded explicit folder or
`HOME/.codex`. Parse TOML with the bundled parser. Preserve a higher positive
integer `features.multi_agent_v2.max_concurrent_threads_per_session` by taking
the maximum. Missing file means no account override. Malformed TOML, invalid
configured limits, and other read errors refuse with `invalid_launch_profile`;
never include file contents or credentials in an error. Read settings only when
selecting a profile; snapshots pin the effective limit for later native effects.
Never read authentication files, sign out, reset usage or write account files.

`validLaunchProfile(value)` checks the saved shape and types; saved effective
Codex limits may exceed 8 to retain a person's higher setting. Null model and
threads represent omitted options. A profile contains no login values.

## Dependencies

- Node crypto supplies deterministic SHA256 names; filesystem reads use the
  injected profileFs port. The bundled `src/vendor/smol-toml/parse.js` supplies
  TOML parsing; no external service or model is required.

Native module only. Prompt interpretation is not configured for these effects.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

Only saved-profile validation/selection and deterministic names are bound. selectLaunchProfile account config/TOML reads and native launch settings remain native. The earlier native-only statement applies to those effects. Native evidence owners: test/workflow-launch-profile.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "374e8ee6d4bb65754b7d89a42b50a4d4220ff344da01b9929eae3ceb9f676460",
  "entries": [
    {
      "operation": "validLaunchProfile",
      "input_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the candidate saved profile. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "boolean"
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "launchProfile",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "string",
            "description": "JSON text encoding of the saved run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "chat": {
            "type": "string",
            "description": "JSON text encoding of the saved chat. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "agent": {
            "type": "string"
          },
          "configDir": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "model": {
            "oneOf": [
              {
                "type": "string"
              },
              {
                "type": "null"
              }
            ]
          },
          "herdrAgentName": {
            "type": "string"
          },
          "codexThreads": {
            "oneOf": [
              {
                "type": "integer"
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "agent",
          "configDir",
          "model",
          "herdrAgentName",
          "codexThreads"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "compute.hash_utf8"
      ]
    },
    {
      "operation": "chatAgentName",
      "input_schema": {
        "type": "object",
        "properties": {
          "profile": {
            "type": "string",
            "description": "JSON text encoding of the selected profile. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "area": {
            "type": "string"
          },
          "run": {
            "type": "string",
            "description": "JSON text encoding of the saved run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "profile",
          "area",
          "run"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "name": {
            "type": "string"
          }
        },
        "required": [
          "name"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "compute.hash_utf8"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "compute",
      "kind": "compute",
      "access": "read",
      "operations": [
        {
          "name": "hash_utf8",
          "access": "read",
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
            "properties": {
              "sha256": {
                "type": "string"
              }
            },
            "required": [
              "sha256"
            ],
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
