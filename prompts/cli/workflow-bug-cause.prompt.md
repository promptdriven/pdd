# Bug cause and explicit issue relations

Own `src/workflow-bug-cause.mjs`. Preserve existing workflows while adding a fixed cause record for reproduced bugs. The agent names the cause and chooses relations; pdd checks evidence and applies only the explicitly selected links. Evidence presence does not prove the diagnosis or relation true.

Export module function `recordBugCause({text, repository, number, root}, ports = {}) -> {json}`. `text` is the reproduce note or summary; repository is owner/name; number is the current positive safe issue number; root is the worktree. Return json as an empty string when neither column-zero label exists (legacy or unreproduced runs). Otherwise require exactly one of each line:

- `Cause: <file>#<function> · Flaw: <one sentence> · Class: <short name>`
- `Relations: <JSON array>` (empty when no other open issues were found).

The agent supplies nonblank file, function, flaw and class. The file must be a safe repository-relative regular Git-visible source file; no absolute paths, traversal, symlinks or outside reads. Read it with `code.read({root,path})`; require the function name to occur literally in that file. Each relation object has exactly `issue` (another positive safe issue number in this repository), `kind` (needs, same cause, same class, duplicate, related), `source` (`issue:N` for that relation's issue or `code:PATH`), `quote` (nonblank exact substring, at most 1000 characters), and `link` (none, blocked by, sub-issue, duplicate). No duplicate issue entries. Read each target through `issues.read({repository,number})`, whose json contains REST issue number, id, node_id, state, title and body; require matching number, open state and no pull_request field. Issue evidence must occur literally in title or body; code evidence uses the same safe source reader. Do not normalize, paraphrase or use fuzzy quote matches.

Validate the complete record and every quote before any link writes. An invalid shape, unsafe path, absent function/quote, closed/non-issue target, repeated/self issue or incompatible link throws code `bug-cause-invalid`. Unavailable evidence throws `bug-cause-unavailable`; no link is written. Do not inspect unmentioned issues or infer additional relations.

Links are separately explicit, because shared cause or class does not by itself establish ordering. A needs relation requires blocked by. A duplicate relation requires duplicate. Same cause allows none or blocked by. Same class allows none or sub-issue. Related requires none. Sub-issue requires that the target title is exactly `Class: ` followed by this cause's class name. Never create a class parent or decide its membership. Call `links.ensure({repository,number,target,kind})` in relation order for non-none links; false or exceptions throw `bug-cause-link-failed`. Earlier successful links survive a later failure; retry observes existing links before writing. Never close an issue or change labels/assignees.

The native link adapter uses the current issue's blocked_by dependency endpoint for blocked by; adds the current issue under the target's sub_issues endpoint for sub-issue (never replaces another parent); and creates GitHub's `Duplicate of #N` comment for duplicate. Paginate current links/comments before adding; an existing link/comment is success. After a new write, reread and require the link/comment to be present before reporting success. Program execution is an injected execFile adapter, passes JSON bodies on stdin, checks nonzero returned status and never interprets agent text as shell. Preserve REST issue IDs as decimal tokens from original API bytes, without rounding through Number. A failed or uncertain write refuses completion; it is not success. Reading existing state on retry prevents confirmed duplicate writes; no exactly-once remote guarantee is claimed.

On success json uses compact JSON with literal non-ASCII characters and keys in the following order. It encodes exactly `file`, `function`, `flaw`, `class`, `relations` (the validated objects unchanged in order), `causeLine` (canonical Cause line) and `relationsLine` (Relations plus compact JSON). These two lines retain the agent's choices in the run record and PR 1. Do not describe cause or link choices as independently proved.

## Dependencies

None. File, issue and link effects use the three injectable ports declared below; native adapters use Git, regular-file reads and gh.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "c85acc6fa1b652338a39461c52dcb275f6c5dc9c60712248e5bf3c6c7429d233",
  "entries": [
    {
      "operation": "recordBugCause",
      "input_schema": {
        "type": "object",
        "properties": {
          "text": {
            "type": "string"
          },
          "repository": {
            "type": "string"
          },
          "number": {
            "type": "integer",
            "minimum": 1,
            "maximum": 9007199254740991
          },
          "root": {
            "type": "string"
          }
        },
        "required": [
          "text",
          "repository",
          "number",
          "root"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "json": {
            "type": "string"
          }
        },
        "required": [
          "json"
        ],
        "additionalProperties": false
      },
      "errors": [
        "bug-cause-invalid",
        "bug-cause-unavailable",
        "bug-cause-link-failed"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "code",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "path": {
                "type": "string"
              }
            },
            "required": [
              "root",
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": {
                "type": "string"
              }
            },
            "required": [
              "content"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "issues",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "repository": {
                "type": "string"
              },
              "number": {
                "type": "integer",
                "minimum": 1,
                "maximum": 9007199254740991
              }
            },
            "required": [
              "repository",
              "number"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "json": {
                "type": "string"
              }
            },
            "required": [
              "json"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "links",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "ensure",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "repository": {
                "type": "string"
              },
              "number": {
                "type": "integer",
                "minimum": 1,
                "maximum": 9007199254740991
              },
              "target": {
                "type": "integer",
                "minimum": 1,
                "maximum": 9007199254740991
              },
              "kind": {
                "type": "string"
              }
            },
            "required": [
              "repository",
              "number",
              "target",
              "kind"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": {
                "type": "boolean"
              }
            },
            "required": [
              "ok"
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
  "conventions": []
}

```
</details>
