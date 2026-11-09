# Approval evidence from a native chat

Own `src/approval-evidence.mjs`. A person can tell a stage agent to approve or
request changes. This module checks for a user message in that stage's native
session after the gate question and returns the original text and session ID for
the caller's journal and status record. It reads files only. The caller owns the
current gate, decision semantics, persistence and application of the decision.
This is recording evidence of a user turn, never authority to approve a gate. The
[runner](workflow-runner.prompt.md#approval-through-the-persons-words) owns explicit
approval authorization; neither even genuine "I approve" text nor freshness proves
that the agent displayed the gate or received consent to advance. Preserve this
reader's public interface and selection rules for recording and changes.

New standalone interface; preserve the worktree/window matching rule from the
existing session-file matcher. A native session ID is optional. When the caller
knows it (pdd started the chat with that ID, or Herdr reported it), only that
session's file can match.

<details>
<summary>Required function, inputs and outcomes</summary>

Export async module function `readApprovalEvidence({stage, gateAskedAt, decision}, ports = {})`.
`decision` is `approve` or `changes`. `stage` has `agent` (`codex` or `claude`),
absolute worktree `root`, finite epoch-millisecond `startedAt` and `endedAt`, and
an optional native `sessionId`. Optional `ignorePrefixes` is a list of text
starts; a user message that starts with one of them (after trimming) is not
evidence. pdd uses it for the change requests it sent itself. A message that
starts with `[Request interrupted` is never evidence.
Those bounds inclusively identify when the native session started, not when its
later approval conversation must end. `gateAskedAt` is finite epoch milliseconds,
at or after stage start, and at or before the observation time. Stage end must be
at or after start and at or before observation time.

Ports optionally supply `fs` (Node promises filesystem), `home`, `env`,
`codexHome`, `claudeConfigDir`, and `now` (a function returning epoch milliseconds).
Defaults are Node's filesystem, OS home, process environment and `Date.now`.
Explicit native roots take precedence over the supplied environment, then the
usual home defaults. Read no other accounts or homes on discovery failure.

Success returns `{ok:true, decision, agent, sessionId, userMessage, userMessageAt}`;
the text is untrimmed and timestamps are epoch milliseconds. Select the latest
eligible user message; ties select the later record in the file. Return no file
contents beyond that message. Failure returns `{ok:false, code, message}` with
one plain, newline-free diagnostic. Codes are `invalid_request`,
`session_not_found`, `session_ambiguous`, `session_unreadable`, and
`user_message_missing`. Never print, throw ordinary filesystem/parse failures,
write files, launch an agent, or grant a decision itself.

</details>

Do not read a file whose last write is older than the stage start; a person's Codex folder can hold many gigabytes. Exactly one native session must match the exact worktree and stage start window. Files with the same session ID (a resumed session) count as one session. A Codex subagent rollout (`thread_source:subagent`, a `parent_thread_id`, or a `source.subagent` object) is never a candidate: step subagents share the worktree cwd but are not the person's chat.
Zero matches refuses; multiple files refuse even if only one has a user reply.
Incomplete discovery must refuse rather than silently discard unreadable files
and manufacture uniqueness. Missing discovery directories mean no matches.
Export async module function `findNativeSessions(stage, ports = {})` for chat
resume and recovery callers: the same stage fields, ports and matching rules
return the distinct matching sessions as `[{id, startedAt}]` (empty when none
match). Incomplete discovery throws code `session_unreadable`; it never returns
an empty list that hides an unreadable file.
Skip symlink entries and refuse over-depth discovery rather than silently truncate.

<details>
<summary>Native identity and user-message rules</summary>

Codex discovery recursively reads `rollout-*.jsonl` under
`(codexHome | env.CODEX_HOME | home/.codex)/sessions`. Its `session_meta`
record supplies UUID `id`, exact `cwd` and start `timestamp`. Accept user text
from `response_item` payloads with `type:message, role:user` (string content or
`input_text`/`text` blocks), and `event_msg` payloads with `type:user_message`
and string `message`. The outer record's timestamp dates the user turn.

Claude discovery reads only direct `*.jsonl` children under
`(claudeConfigDir | env.CLAUDE_CONFIG_DIR | home/.claude)/projects/<escaped cwd>`.
Escape every non-ASCII-alphanumeric cwd character to `-`, as native Claude does.
Use the first main conversation record carrying UUID `sessionId`, `cwd` and
`timestamp` as identity/start. Native Claude needs no Codex `session_meta` record.
Only `type:user` with `message.role:user`, matching session/cwd, and string or
`text` content counts. Exclude `isMeta`, `isSidechain`, tool-result-only content,
and `subagents` directories. Claude writes user rows that no person typed:
when a row has `origin`, only `origin.kind:"human"` counts (not `task-notification`
or `peer`); skip `isCompactSummary` and `isVisibleInTranscriptOnly` rows; and skip
text that starts with `<task-notification>`, `<system-reminder>` or `<local-command-`
(older versions write those without `origin`). A later conflicting identity invalidates the file.

Text blocks join with newlines; blank-only text cannot serve as evidence.
Timestamps accept finite epoch milliseconds or parseable date strings. The
message must be strictly after the gate and no later than observation time.
Assistant, developer, tool and system records cannot serve as user evidence.
Codex can store generated environment context and AGENTS instructions in user-role
records. Exclude messages consisting only of `<environment_context>` or
`<permissions instructions>` wrappers, and messages beginning with the generated
`# AGENTS.md instructions for ` heading or with `# AGENTS.md instructions` followed by `<INSTRUCTIONS>`. These are not a person's reply; role
alone does not make these known generated records evidence.
Recognizing wrapper-only context must take linear time in the message length,
including repeated opening/closing tags followed by ordinary user text. Preserve
the same exclusion for concatenated complete wrappers with whitespace between them;
an incomplete wrapper or a non-wrapper suffix is user text.
Malformed complete records in a matched file refuse; an unterminated final line
is an in-progress write and never serves as evidence. A matched file's metadata
and messages come from the same read snapshot.

</details>

## Dependencies

- [Prompting guide](../../docs/prompting-guide.md): authoring and generation.
- [Public boundary](public-boundary.prompt.md): authoring and verification; use
  Node built-ins only, with no services or private runtime dependencies.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

The fs resource supplies the existing promises filesystem replies and clock.now supplies ports.now. This checks supplied-session selection and message exclusion only. Authentic session provenance, physical identity and concurrent host snapshots remain native; returned text never approves a gate. Native evidence owners: test/approval-evidence-budget.test.mjs, test/approval-evidence.test.mjs.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "525f1893f4f2b82d1282ffa292d6a9be63ce037e9bbe2a23b6d042f5674330fa",
  "entries": [
    {
      "operation": "readApprovalEvidence",
      "input_schema": {
        "type": "object",
        "properties": {
          "stage": {
            "type": "string",
            "description": "JSON text encoding of the native stage identity and bounds. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "gateAskedAt": {
            "type": "number"
          },
          "decision": {
            "type": "string",
            "enum": [
              "approve",
              "changes"
            ]
          },
          "ignorePrefixes": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "required": [
          "stage",
          "gateAskedAt",
          "decision"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the success evidence or ok:false/code/message reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "fs.readdir",
        "fs.stat",
        "fs.readFile",
        "clock.now"
      ]
    },
    {
      "operation": "findNativeSessions",
      "input_schema": {
        "type": "object",
        "properties": {
          "stage": {
            "type": "string",
            "description": "JSON text encoding of the native stage identity and bounds. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "stage"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the distinct id/startedAt sessions. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [
        "session_unreadable"
      ],
      "resource_operations": [
        "fs.readdir",
        "fs.stat",
        "fs.readFile",
        "clock.now"
      ]
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "fs",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readdir",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing fs.readdir dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
        },
        {
          "name": "stat",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing fs.stat dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
        },
        {
          "name": "readFile",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "string",
                "description": "JSON text encoding of the positional arguments to the existing fs.readFile dependency operation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
      "name": "clock",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "now",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "number"
              }
            },
            "required": [
              "value"
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
