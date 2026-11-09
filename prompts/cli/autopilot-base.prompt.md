# Automatic run base

Own `src/autopilot-base.mjs`. The authorized scope is issue #3071 points 1–3. Preserve manual workflow base selection, approval, trust, checks, merge authority and stacked PR behavior. This module only reads; it never merges or changes branches or documents.

`selectAutopilotBase({cwd,defaultBranch}, ports={})` returns one branch name. Read `pdd.json` from cwd through `readConfig(cwd)` (native default: JSON filesystem read; a missing file means an empty config). Use `autopilot.base` when present; otherwise use the supplied repository default. A configured base must be a nonempty string naming a branch, excluding HEAD, options and full refs. Validate `refs/heads/BRANCH` with Git through `execFile`. Invalid config or an unavailable default fails without inventing a branch. Slash-separated names are allowed.

`checkAutopilotBase({run,pr}, ports={})` returns `{exitCode,message}`. `run` is the saved workflow run; `pr` is a positive PR number string. Refuse missing run identity, saved base or a PR not published by that run. Before any automatic merge, read that PR fresh from its saved repository, and require its actual base to equal `run.baseBranch`; stacked code PRs must first be retargeted through the existing merge route. The saved base remains the audit authority even if configuration changes later. Read the current default branch and all releases fresh. Choose the non-draft release with the newest published_at, including prereleases; no releases means only the default ancestry check applies. Use GitHub compare for default...saved-base and release-tag...saved-base. Each must have behind_by zero and status identical or ahead. Missing, malformed or failed observations refuse with a finite reason. Refuse an old or divergent base with a reason naming the branch and the default or release tag it lacks. After a merge the same read checks that the merged PR went to the saved base. A successful read reports the PR, base, default and release tag (or no release). Exit 0 means these base checks pass; exit 1 means refused. It does not approve a merge or prove tests or reviews.

All program calls use injected `execFile(file,args,{cwd})`; all config reads use `readConfig`. Native defaults use local filesystem and the counted native GitHub process adapter. No error includes raw external output or secrets. GitHub requests are read-only, with explicit repository paths and encoded refs. No cache is used for merge safety.

## Dependencies

- [Workflow runs](workflow-runs.prompt.md): required native generation context for the saved run repository, PR records and baseBranch supplied by the launcher.
- [GitHub calls](github-calls.prompt.md): required native generation context for the default counted process adapter.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

config.readConfig binds readConfig(cwd); program.execFile binds the actual execFile(file,args,{cwd}) port. Supplied Git/GitHub observations check base decisions only. Real ancestry, repository identity and fresh live reads remain native; neither entry grants merge authority. Native evidence owners: test/autopilot-base.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "aee6c6a3124ac7d9fa88c8ecb71d119c22071138b2c73eab7e4c1eda2870e707",
  "entries": [
    {
      "operation": "selectAutopilotBase",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "defaultBranch": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "defaultBranch"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "branch": {
            "type": "string"
          }
        },
        "required": [
          "branch"
        ],
        "additionalProperties": false
      },
      "errors": [
        "Error"
      ],
      "resource_operations": [
        "config.readConfig",
        "program.execFile"
      ]
    },
    {
      "operation": "checkAutopilotBase",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "string",
            "description": "JSON text encoding of the saved run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "pr": {
            "type": "string"
          }
        },
        "required": [
          "run",
          "pr"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exitCode": {
            "type": "integer"
          },
          "message": {
            "type": "string"
          }
        },
        "required": [
          "exitCode",
          "message"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "program.execFile"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "config",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readConfig",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing config.readConfig dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              },
              "error": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "value",
              "error"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "program",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "execFile",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing program.execFile dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "args"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the dependency reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              },
              "error": {
                "oneOf": [
                  {
                    "type": "string"
                  },
                  {
                    "type": "null"
                  }
                ]
              }
            },
            "required": [
              "value",
              "error"
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
