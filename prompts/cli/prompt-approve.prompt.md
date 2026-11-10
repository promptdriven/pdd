# Prompt approve

Own `src/prompt-approve.mjs`. Export `runApprove({words, cwd, said}, ports)` (returns an exit code) and `approvePromptText(text)` (returns the approved text or null). `pdd approve PROMPT` is the one way pdd sets `"status": "approved"`. It records a person's decision through terminal y/N or, in easy mode, an agent-supplied `--said` value after the person approves in chat. Preserve existing exports, including `presentAndApprove`, and the Simulator callback behavior; this command adds no Simulator approval route.

## Steps

1. PROMPT is one path (relative to cwd). It must be a Git-visible `*.prompt.md` file in the repo (`git rev-parse --show-toplevel`), else exit 2: `<path> is not a Git-visible *.prompt.md file in this repository.`
2. Resolve repository policy through the required shared owner before any write. In strict mode --said always refuses before reading stdin. After policy/configuration prechecks, resolve present `said` through the shared person-words helper; invalid or blank input exits 2 without changes. Keep accepted words verbatim. Without said, easy mode retains its existing both-TTY requirement; strict mode additionally excludes agent-marker and current workflow-chat-pane invocations. A refused route uses exit 2, `pdd approve is for a person at a terminal. Ask the person to run: pdd approve <path>`. Nothing changes.
3. Read the prompt through the required shared authored-file reader. Use its expanded interface and numeric source tokens. Missing/duplicate blocks, invalid JSON, unsafe/missing/cyclic contract references and schema problems refuse with the same reason as lint/test before any question or write. Keep the authored bytes for the edit and prose view. A reader source/reference failure returns the same declined result and reason to the Simulator callback; it must not escape before the callback can record that refusal.
4. For a parsed interface, check the Simulator's expectedHash before schema diagnostics: a different prose hash declines with the existing changed-prompt reason and no question or write. After the shared parse/schema checks pass, approved and the hash is current: print `<path> is already approved and current.` and exit 0.
5. Use the shared reader's `promptSchemaRefusals` for the prompt and called prompts. Print every problem with its code, section, message and fix hint, then `Fix these before you approve.`, exit 4. Contract references stay authored references on disk; the approval view shows their resolved fields, types and constraints.
6. Show the interface in plain words: `<path> (<status>)`, then for each entry `Operation <name>`, `Input:` and `Result:` with one line for each field (`name: type, rule`; nested lists and objects indented; a field not in `required` is `(optional)`; an enum is its values; `oneOf` is its variants joined with `or`), and `Errors: …`. Then the calls and resources when there are any. When interface declarations changed since the last approved Git version, show a full interface diff before the prose view. Without an approved Git version, use the drafter’s saved pre-extension body only when its recorded interface hash matches the current draft. Label that baseline as before extension; it is display context, never approval evidence. The single global Runtime status cannot represent mixed approval: state that the whole interface needs re-approval. Show unchanged declaration pointers and the old serialized bytes alongside additions; do not imply that only additions are approved. Preserve historical approval evidence. Show the current coverage report from the interface drafter, including each quoted sentence, status, exact field and retained meaning. If any sentence is unmapped or conflicting, present one grouped decision asking whether to amend prose, amend the declaration or accept the authored contract as written. This is evidence for a person, not a schema refusal. Automatic approval cannot cross this decision. Then the text that the person approves (round-2 tester: the screen showed only the interface, and the change was in the prose). The prose is the file text without the interface block. The last approved version is the newest Git commit (of the last 200 that touch the file) whose version of the file has `"status": "approved"` with a `prose_sha256` that equals its own prose hash. With one: `Text changes since the last approved version (<first 12 of its commit>):` and the changed lines, `  - ` for a removed line and `  + ` for an added one, with 1 unchanged line around each change (`    ` in front) and `  …` between parts; or `Text: the same as the last approved version (<commit>).` With none: `Text (no approved version in Git, so all of it):` and every prose line, 2 spaces in, without the empty lines at the end. Show at most 40 of these lines, then `… N more lines not shown.` and `See all of them with: git diff <commit> -- <path>` (or `Read the whole file: <path>`). Never cut inside a line; remove control characters so that terminal codes cannot hide text. When the prompt was approved but its text changed: `The text changed after it was approved. Read the prompt again before you answer.`
A coverage reader limitation with code `interface-contract-invalid` at `/dependencies`
(such as an unsupported fragment or context cycle) is incomplete coverage evidence,
not a schema refusal. Show `coverage-context-unavailable`, its exact diagnostic,
and an explicit decision to accept the authored declaration and prose with that
coverage gap. Do not fabricate mapped rows or claim a coverage pass. Retain the
normal terminal/said decision and every prior parse, schema and contract-reference
refusal. Other coverage errors still refuse. Automatic approval remains blocked
by any unavailable coverage and runs no native tests or Runtime checks.

7. With valid said in easy mode, use the resolved words as the decision without another stdin read or a native conversation-log lookup. Otherwise ask `Approve <path>? y/n ` and read one line. On the terminal route only `y` or `yes` (any case) approves. Anything else, or no answer: `Not approved. Nothing changed.`, exit 1.
8. On terminal yes or accepted said: set the top-level `"status"` to `"approved"` and the top-level `"prose_sha256"` to the current prose hash, and keep every other byte (a nested `status` field is never touched). Check that the new text parses to the same interface with only those two values changed and that its prose hash is unchanged. Append durable evidence through the shared owner, with the current path/hash, invoking actor, route, clock time and verbatim words (null for terminal). Print `Approved <path>.`, the approved path/hash and a short evidence line; exit 0 only after evidence is saved. Already-approved/current files keep their existing no-op output and do not invent another approval. If the block has no `prose_sha256` key, exit 4: `Add "prose_sha256": "" to the Runtime interface, then run pdd approve again.`

Runtime transport wraps `approvePromptText(text)` as `{text}` with text null when the owner declines the update; `runApprove` wraps its numeric exit code as `{exitCode}` and catches errors into exit codes. It calls the shared `approval-policy` owner for `readApprovalPolicy`, `approvalActor`, `readSaidWords`, `readPromptApprovals` and `recordPromptApproval`. The journal receives the caller-created id and complete evidence. Bind process context and random event identity through `process.environment` and `ids.randomUUID`, Git through `git.execFile`, prompt file operations through `files.stat/read/write`, terminal words through `stdin.read`, time through `clock.now` and output through `output.stdout/stderr`. The approval-policy owner owns repository policy and durable journal decisions; do not replace those calls with policy result ports.

## Native-only and automatic approval

Show a native-only declaration's kind and reason before approval. It is eligible for the existing person routes after kind/reason validation, without entry schemas or limits. Record the kind and reason with its path/hash. Validate before the already-approved fast path too.

`pdd approve PROMPT --automatic --tests COMMAND` invokes the interface drafting owner's automatic-check-pass route. Never combine it with --said. Strict approval mode still requires a person and refuses this route. Only a valid unchanged draft from this command with no unmapped or conflicting contract sentences, with committed unchanged prose and existing code/tests, can qualify. This route does not approve new behavior or native-only blocks. Keep ordinary person routes unchanged.

## Dependencies

- [Automatic draft approval](interface-draft.prompt.md): required generation and verification context for `runAutomaticApproval`, `contractCoverage` and `coverageView`. The caller consumes this public operation; ordinary person approval policy remains here.

- [Shared authored-file reader](runtime-preflight.prompt.md#shared-authored-file-reader): required generation/verification/testing context for parsing, references, numeric tokens and schema refusals.

- [Approval policy and journal](approval-policy.prompt.md): required authoring/generation/native-production/verification/testing context for config, actor, evidence shape and storage.

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md).

## Caller navigation

The [CLI](pdd-cli.prompt.md) routes `pdd approve PROMPT` here. The [runtime client](runtime-client.prompt.md) uses the same view and edit for Try-page approvals.

Use “Runtime interface” when naming the declaration and its global approval status in user messages.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "8e807397ce37b4af0227dd6197db4415edb4a71d51b8b9b3397cc551f8729cc0",
  "entries": [
    {
      "operation": "approvePromptText",
      "input_schema": {
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
          "text": {
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
          "text"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": []
    },
    {
      "operation": "runApprove",
      "input_schema": {
        "type": "object",
        "properties": {
          "words": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "cwd": {
            "type": "string"
          },
          "said": {
            "type": "string"
          },
          "automatic": {
            "type": "boolean"
          },
          "tests": {
            "type": "string"
          }
        },
        "required": [],
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
        "git.execFile",
        "files.stat",
        "files.read",
        "files.write",
        "clock.now",
        "output.stdout",
        "output.stderr",
        "ids.randomUUID",
        "process.environment",
        "stdin.read",
        "git.spawnSync"
      ]
    }
  ],
  "calls": [
    {
      "operation": "runApprove",
      "target": "prompts/cli/approval-policy.prompt.md",
      "target_operation": "readApprovalPolicy",
      "max_calls": 1
    },
    {
      "operation": "runApprove",
      "target": "prompts/cli/approval-policy.prompt.md",
      "target_operation": "approvalActor",
      "max_calls": 2
    },
    {
      "operation": "runApprove",
      "target": "prompts/cli/approval-policy.prompt.md",
      "target_operation": "readSaidWords",
      "max_calls": 1
    },
    {
      "operation": "runApprove",
      "target": "prompts/cli/approval-policy.prompt.md",
      "target_operation": "readPromptApprovals",
      "max_calls": 1
    },
    {
      "operation": "runApprove",
      "target": "prompts/cli/approval-policy.prompt.md",
      "target_operation": "recordPromptApproval",
      "max_calls": 1
    }
  ],
  "resources": [
    {
      "name": "git",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "execFile",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
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
              "args",
              "cwd"
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
        },
        {
          "name": "spawnSync",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "args": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "cwd": {
                "type": "string"
              },
              "maxBuffer": {
                "type": "integer",
                "minimum": 0
              }
            },
            "required": [
              "args",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "status": {
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
              "status",
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
      "kind": "blob",
      "access": "write",
      "operations": [
        {
          "name": "stat",
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
              "exists": {
                "type": "boolean"
              },
              "size": {
                "type": "integer",
                "minimum": 0
              },
              "is_symlink": {
                "type": "boolean"
              }
            },
            "required": [
              "exists",
              "size",
              "is_symlink"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "read",
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
              "content": {
                "type": "string"
              }
            },
            "required": [
              "content"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              },
              "content": {
                "type": "string"
              }
            },
            "required": [
              "path",
              "content"
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
    },
    {
      "name": "clock",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "now",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "now": {
                "type": "number"
              }
            },
            "required": [
              "now"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "stdout",
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
        },
        {
          "name": "stderr",
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
    },
    {
      "name": "ids",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "randomUUID",
          "access": "write",
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
                "type": "string"
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
      "name": "process",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "environment",
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
              "env": {
                "type": "string"
              }
            },
            "required": [
              "env"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "stdin",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "read",
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
              "text": {
                "type": "string"
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
              "text",
              "error"
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
  "conventions": [
    {
      "path": "/resources/5/operations/0/result_schema/properties/env",
      "convention": "json"
    }
  ]
}```
</details>
