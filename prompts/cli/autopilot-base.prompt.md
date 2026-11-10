# Automatic run base

Own `src/autopilot-base.mjs`. The authorized scope is issue #3071 points 1–3. Preserve manual workflow base selection, approval, trust, checks, merge authority and stacked PR behavior. This module only reads; it never merges or changes branches or documents.

`selectAutopilotBase({cwd,defaultBranch}, ports={})` returns one branch name. Read `pdd.json` from cwd through `readConfig(cwd)` (native default: JSON filesystem read; a missing file means an empty config). Use `autopilot.base` when present; otherwise use the supplied repository default. A configured base must be a nonempty string naming a branch, excluding HEAD, options and full refs. Validate `refs/heads/BRANCH` with Git through `execFile`. Invalid config or an unavailable default fails without inventing a branch. Slash-separated names are allowed.

`checkAutopilotBase({run,pr}, ports={})` returns `{exitCode,message}`. `run` is the saved workflow run; `pr` is a positive PR number string. Refuse missing run identity, saved base or a PR not published by that run. Before any automatic merge, read that PR fresh from its saved repository, and require its actual base to equal `run.baseBranch`; stacked code PRs must first be retargeted through the existing merge route. The saved base remains the audit authority even if configuration changes later. Read the current default branch and all releases fresh. Choose the non-draft release with the newest published_at, including prereleases; no releases means only the default ancestry check applies. Use GitHub compare for default...saved-base and release-tag...saved-base. Each must have behind_by zero and status identical or ahead. Missing, malformed or failed observations refuse with a finite reason. Refuse an old or divergent base with a reason naming the branch and the default or release tag it lacks. After a merge the same read checks that the merged PR went to the saved base. A successful read reports the PR, base, default and release tag (or no release). Exit 0 means these base checks pass; exit 1 means refused. It does not approve a merge or prove tests or reviews.

All program calls use injected `execFile(file,args,{cwd})`; all config reads use `readConfig`. Native defaults use local filesystem and the counted native GitHub process adapter. No error includes raw external output or secrets. GitHub requests are read-only, with explicit repository paths and encoded refs. No cache is used for merge safety.

## Dependencies

- [Workflow runs](workflow-runs.prompt.md): required native generation context for the saved run repository, PR records and baseBranch supplied by the launcher.
- [GitHub calls](github-calls.prompt.md): required native generation context for the default counted process adapter.

Runtime transport: each entry names the public operation above. `selectAutopilotBase` returns `{branch}` and raises `invalid-base-config` when `config.readConfig({cwd})` fails or returns non-object JSON, or `invalid-base-branch` when the selected branch name is invalid (`HEAD`, leading `-`, `refs/` prefix, blank) or `program.execFile` for `git check-ref-format refs/heads/<branch>` exits nonzero. `checkAutopilotBase` takes `{run, pr}` and returns `{exitCode, message}` using `program.execFile({file, args, cwd})`: on success (`exitCode: 0`), `message` is `Base check: PR #<pr> targets saved base <base>; contains default branch <defaultBranch> and newest release tag <tag_name>.` (or `no published release is present`); on refusal (`exitCode: 1`), `message` starts with `Automatic merge refused: `, including `Automatic merge refused: <base> does not contain <description> <ref> (<behind_by> commit(s) behind).` when behind (`description` is `default branch` or `newest release tag`). Native filesystem reading and counted child-process execution stay a native obligation covered by `test/autopilot-base.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "a30ead3c473aa6624e47d473b3055e9899c2e53220634aaf7db78f60375d8235",
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
        "invalid-base-config",
        "invalid-base-branch"
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
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "repo": {
                "type": "string"
              },
              "baseBranch": {
                "type": "string"
              },
              "pr": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "number": {
                      "type": "integer"
                    }
                  },
                  "required": [
                    "number"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "root",
              "repo",
              "baseBranch",
              "pr"
            ],
            "additionalProperties": false
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
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "raw": {
                "type": "string",
                "description": "JSON text of pdd.json (use \"{}\" when missing)."
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
              "raw",
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
              "file": {
                "type": "string"
              },
              "args": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "file",
              "args",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "stdout": {
                "type": "string"
              },
              "exitCode": {
                "type": "integer"
              }
            },
            "required": [
              "stdout",
              "exitCode"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 32,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
