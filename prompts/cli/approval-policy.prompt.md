# Approval policy and durable prompt evidence

Own new `src/approval-policy.mjs`, the small shared boundary used by standalone and workflow approval. It owns repository policy, invoking-actor identification and the durable prompt journal. It never decides that a person approved, changes a prompt, publishes or merges.

## Repository policy

Module function `readApprovalPolicy({root}, ports = {})` returns `{strictApprovals}`. Read only `pdd.json` directly in the trusted repository root supplied by the caller. Missing file or missing `strict_approvals` means false; false means easy; true means terminal-only. Require a JSON object and a boolean when that key exists. Unknown keys do not affect approval. Malformed JSON, wrong type and unreadable existing config fail with a finite diagnostic naming `pdd.json`; callers must stop before any approval mutation. Do not consult caller subdirectories, `pdd-source.json` or user agent configuration. Standalone approval resolves the target checkout's Git top-level root from cwd. Workflow approval supplies the run's trusted main checkout `sourceRoot`, never the agent-editable `run.root`; changing or deleting the worktree's config cannot weaken main-checkout strict policy. Never fall back after a read error.

## Person words input

Module function `readSaidWords(said, ports = {})` returns the verbatim text argument, except that the exact marker `-` reads the entire UTF-8 stdin stream once through injected `stdin` and returns it as one payload. Preserve trailing newlines, quotes, backticks and dollar signs. Do not split lines, trim stored text, interpolate it or grade its meaning. Reject nonstring or blank-only payloads with a finite diagnostic. A read failure refuses without approval. Callers resolve policy, strict-mode refusal and their configuration preconditions before invoking this helper, so strict refusals consume no stdin. This shared native helper is the only owner of stdin marker interpretation; CLI dispatch forwards the marker unchanged.

Templates for person text use a quoted heredoc with a delimiter absent from that text. For example:

```sh
pdd workflow approve N --said - <<'PDD_SAID'
<the person's words>
PDD_SAID
```

Choose another quoted delimiter if a complete person-text line equals `PDD_SAID`. Literal `--said` arguments remain supported for simple text. Neither form authorizes pdd to judge the person's intent.

## Actor and evidence

Module function `approvalActor({env})` returns `{kind,id}` describing the invoker, never claiming authenticated identity of the person whose words were supplied. Prefer concrete available session identity: a nonempty `CODEX_THREAD_ID` makes kind `agent` and id `CODEX_THREAD_ID=VALUE` (identifying Codex and its session). Otherwise a nonempty `CLAUDECODE` identifies the Claude invoker as `CLAUDECODE=VALUE`; do not claim it is a session ID. Only then fall back to nonempty `PDD_AGENT_SESSION` as `PDD_AGENT_SESSION=VALUE`. A generic PDD_AGENT_SESSION=1 must never hide a concrete Codex session. Otherwise kind is `terminal`, id is `USER`, falling back to `LOGNAME`, then `unknown`. Preserve the selected value verbatim; presentation safety belongs to the publisher. Reject environment values containing NUL (`\u0000`) with `invalid-actor-env`.

An approval evidence record is `{id,route,actor,at,words,prompts}`. `id` is a nonempty string identifying one approval event independently of its evidence content or clock; new events have distinct identities even with identical route/actor/time/words/prompts. Copies of the same event in gate history and the journal retain the same id; retries retain it. Legacy evidence without id remains readable and does not acquire fabricated historical provenance. Identity allocation uses injected native dependencies when it needs external state; no particular encoding or private allocation algorithm is required. `route` is `said`, `terminal`, `chat` (existing native Herdr evidence), `automatic-check-pass`, `card-choice` or `prompt-reentry`. The last three are pdd's own records for a workflow run ([normal-run gates](workflow-runner.prompt.md#normal-run-gates)): `automatic-check-pass` for a prompt PR gate that a verified full check pass opened, and `card-choice` for the code gate that the person's Story-card choice covers. `prompt-reentry` records resuming an existing code scope after a returned automatic prompt repair. Its `basis` names `priorCodeApprovalId` and `storyEvidenceId`; it requires the runner's current scoped operator delegation and passing source checks. The runner also uses `automatic-check-pass` for that returned automatic prompt publication. These records have null `words` and may have a `basis` object that names the earlier evidence id and the check batches. They are never a person's later reply. `actor` is the invoking identity above; `at` is the approval command's epoch-millisecond clock value, not a fabricated chat timestamp. `words` is the exact supplied --said value, the exact native chat message for chat, or null for terminal. Each `prompts` row is `{path,proseSha256}`: repository-relative POSIX path and current lowercase SHA-256. Empty prompt arrays are valid for gates without changed prompts. Native chat session/message-time fields remain in their existing run fields. These are local provenance claims, not cryptographic proof of a speaker.

Module function `recordPromptApproval({commonDir,evidence}, ports = {})` appends the evidence to `<commonDir>/pdd/approvals.json`; module function `readPromptApprovals({commonDir}, ports = {})` returns its records, missing file as an empty list. The journal is `{v:1,approvals:[...]}`; reject malformed/unreadable existing journals and never silently replace them. Shared Git-common-dir storage lets linked worktrees find standalone approvals. Preserve all previous records and verbatim words, write via temporary file and rename, and serialize concurrent updates so successful approvals are not lost. No credentials or native conversation log is copied. Journal locking recovers an observed empty `approvals.lock` directory or a stale lock whose recorded PID is confirmed dead on this hostname. Empty-directory recovery must not delete a newly published owner; preserve replacement ownership. If a lock disappears during contention inspection or reclamation (ENOENT), retry acquisition rather than fail approval. Preserve alive, foreign-host, malformed, unverifiable and permission-denied owners. Publish ownership atomically; release or reclaim only the observed owner, so a replacement owner's lock is never deleted. Native-only injected ports are `fs`, `now`, `env`, `hostname` (a function or string), `ownerPid`, and `processIdentity(pid)` returning `{alive: true|false|undefined}`, with native defaults matching #2677 owner-liveness semantics. Only `alive === false` confirms death. Exceptions, including EPERM, and undefined liveness are unverifiable and preserve the owner. Share the #2677 owner-liveness semantics without importing the workflow runner or creating a required-context cycle. File operations and clock/identity inputs are injected through native ports (`fs`, `env`, `now`) with real defaults; Git root/commonDir resolution stays with callers.

The optional native port `afterApprovalLock()` is an asynchronous caller guard. Await it after acquiring journal custody and before reading or preparing the journal. A rejection propagates unchanged, preserves the existing journal and releases this writer's custody. The caller supplies fresh asynchronous authority observations here and uses the synchronous commit guard below for current policy and progress. Missing guards preserve ordinary append behavior.

The optional native port `beforeApprovalCommit()` is a synchronous caller guard. After acquiring journal custody, invoke it immediately before renaming the prepared journal into place, with no asynchronous wait between guard and rename. It returns no value; a thrown error refuses the append and propagates unchanged. On refusal, preserve the existing journal bytes, remove the temporary journal and release only this writer's lock ownership. An absent guard preserves ordinary append behavior. The caller owns eligibility policy; the journal only supplies the guarded commit boundary so eligibility cannot be taken from before a contention wait.

Callers prevalidate journal readability and all selected prompt edits before mutation. A failed prompt or journal write never reports success or advances a gate; report any prompt paths already changed if rollback cannot complete. A journal row applies to PR evidence only when its path and hash both match the current published prompt. Later prose invalidates that association. Gate history and standalone journal may describe the same approval: publish copies of the same identified event once without deleting local history; distinct event ids must remain distinct even when all evidence content matches. Only id-less legacy records may use content equality for deduplication.

## Automatic draft evidence

The journal also accepts route `automatic-check-pass`. Such records have null words and retain native test command and success, the complete current prompt-check result, draft provenance, source hashes and prompt kind. This is a distinct route, never relayed person words. Person records may also retain each prompt's kind and native-only reason. The interface drafting owner checks eligibility and current evidence before calling this journal.

## Dependencies

No other business prompt supplies policy. Bind config and journal file access through `files.stat`, `files.read` and `files.write`, stdin marker reads through `stdin.read`, event ID allocation through `ids.randomUUID`, journal lock custody through `lock.acquire` and `lock.release`, and caller commit guards through `guards.afterApprovalLock` and `guards.beforeApprovalCommit`. `readApprovalPolicy({root})` returns `{strictApprovals}` or raises `invalid-approval-policy`; `readSaidWords({said})` returns `{words}` or raises `invalid-said-words`; `approvalActor({env})` returns `{kind, id}` or raises `invalid-actor-env`; `readPromptApprovals({commonDir})` returns `{approvals}` or raises `invalid-approval-journal`; and `recordPromptApproval({commonDir, evidence})` returns `{record, count}` or raises `invalid-approval-evidence`, `approval-lock-busy`, `invalid-approval-journal` or `guard-refused`. Native filesystem concurrency, OS process-liveness probes, atomic rename and Git common-directory resolution remain native obligations (`test/approval-lead-fixes.test.mjs`, `test/approval-round2.test.mjs`, `test/autopilot-pr1-gate.test.mjs`, `test/autopilot.test.mjs`, `test/native-evidence-intake.test.mjs`).

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "c35e0d0372a7f2b6fa3e90a36ddb55631879d07549c024c672e8e2923c829837",
  "entries": [
    {
      "operation": "readApprovalPolicy",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": { "type": "string" }
        },
        "required": ["root"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "strictApprovals": { "type": "boolean" }
        },
        "required": ["strictApprovals"],
        "additionalProperties": false
      },
      "errors": ["invalid-approval-policy"],
      "resource_operations": ["files.stat", "files.read"]
    },
    {
      "operation": "readSaidWords",
      "input_schema": {
        "type": "object",
        "properties": {
          "said": { "type": "string" }
        },
        "required": ["said"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "words": { "type": "string" }
        },
        "required": ["words"],
        "additionalProperties": false
      },
      "errors": ["invalid-said-words"],
      "resource_operations": ["stdin.read"]
    },
    {
      "operation": "approvalActor",
      "input_schema": {
        "type": "object",
        "properties": {
          "env": {
            "type": "object",
            "properties": {
              "CODEX_THREAD_ID": { "type": "string" },
              "CLAUDECODE": { "type": "string" },
              "PDD_AGENT_SESSION": { "type": "string" },
              "USER": { "type": "string" },
              "LOGNAME": { "type": "string" }
            },
            "required": [],
            "additionalProperties": false
          }
        },
        "required": ["env"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "kind": { "type": "string", "enum": ["agent", "terminal"] },
          "id": { "type": "string" }
        },
        "required": ["kind", "id"],
        "additionalProperties": false
      },
      "errors": ["invalid-actor-env"],
      "resource_operations": []
    },
    {
      "operation": "readPromptApprovals",
      "input_schema": {
        "type": "object",
        "properties": {
          "commonDir": { "type": "string" }
        },
        "required": ["commonDir"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "approvals": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": { "type": "string" },
                "route": {
                  "type": "string",
                  "enum": [
                    "said",
                    "terminal",
                    "chat",
                    "automatic-check-pass",
                    "card-choice",
                    "prompt-reentry"
                  ]
                },
                "actor": {
                  "type": "object",
                  "properties": {
                    "kind": { "type": "string", "enum": ["agent", "terminal"] },
                    "id": { "type": "string" }
                  },
                  "required": ["kind", "id"],
                  "additionalProperties": false
                },
                "at": { "type": "number" },
                "words": {
                  "oneOf": [
                    { "type": "string" },
                    { "type": "null" }
                  ]
                },
                "prompts": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "path": { "type": "string" },
                      "proseSha256": { "type": "string" }
                    },
                    "required": ["path", "proseSha256"],
                    "additionalProperties": false
                  }
                }
              },
              "required": ["id", "route", "actor", "at", "words", "prompts"],
              "additionalProperties": false
            }
          }
        },
        "required": ["approvals"],
        "additionalProperties": false
      },
      "errors": ["invalid-approval-journal"],
      "resource_operations": ["files.stat", "files.read"]
    },
    {
      "operation": "recordPromptApproval",
      "input_schema": {
        "type": "object",
        "properties": {
          "commonDir": { "type": "string" },
          "evidence": {
            "type": "object",
            "properties": {
              "id": { "type": "string" },
              "route": {
                "type": "string",
                "enum": [
                  "said",
                  "terminal",
                  "chat",
                  "automatic-check-pass",
                  "card-choice",
                  "prompt-reentry"
                ]
              },
              "actor": {
                "type": "object",
                "properties": {
                  "kind": { "type": "string", "enum": ["agent", "terminal"] },
                  "id": { "type": "string" }
                },
                "required": ["kind", "id"],
                "additionalProperties": false
              },
              "at": { "type": "number" },
              "words": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              },
              "prompts": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "path": { "type": "string" },
                    "proseSha256": { "type": "string" }
                  },
                  "required": ["path", "proseSha256"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["route", "actor", "at", "words", "prompts"],
            "additionalProperties": false
          }
        },
        "required": ["commonDir", "evidence"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "record": {
            "type": "object",
            "properties": {
              "id": { "type": "string" },
              "route": { "type": "string" },
              "actor": {
                "type": "object",
                "properties": {
                  "kind": { "type": "string" },
                  "id": { "type": "string" }
                },
                "required": ["kind", "id"],
                "additionalProperties": false
              },
              "at": { "type": "number" },
              "words": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              },
              "prompts": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "path": { "type": "string" },
                    "proseSha256": { "type": "string" }
                  },
                  "required": ["path", "proseSha256"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["id", "route", "actor", "at", "words", "prompts"],
            "additionalProperties": false
          },
          "count": { "type": "integer" }
        },
        "required": ["record", "count"],
        "additionalProperties": false
      },
      "errors": [
        "invalid-approval-evidence",
        "approval-lock-busy",
        "invalid-approval-journal",
        "guard-refused"
      ],
      "resource_operations": [
        "lock.acquire",
        "lock.release",
        "guards.afterApprovalLock",
        "guards.beforeApprovalCommit",
        "ids.randomUUID",
        "compute.hash_utf8",
        "files.stat",
        "files.read",
        "files.write"
      ]
    }
  ],
  "calls": [],
  "resources": [
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
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exists": { "type": "boolean" },
              "size": { "type": "integer", "minimum": 0 },
              "is_symlink": { "type": "boolean" }
            },
            "required": ["exists", "size", "is_symlink"],
            "additionalProperties": false
          }
        },
        {
          "name": "read",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": { "type": "string" }
            },
            "required": ["content"],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" },
              "content": { "type": "string" }
            },
            "required": ["path", "content"],
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
      "name": "stdin",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "read",
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
              "text": { "type": "string" },
              "error": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              }
            },
            "required": ["text", "error"],
            "additionalProperties": false
          }
        }
      ]
    },
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
              "text": { "type": "string" }
            },
            "required": ["text"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": { "type": "string" }
            },
            "required": ["value"],
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
              "id": { "type": "string" }
            },
            "required": ["id"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "lock",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "acquire",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "commonDir": { "type": "string" }
            },
            "required": ["commonDir"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "acquired": { "type": "boolean" }
            },
            "required": ["acquired"],
            "additionalProperties": false
          }
        },
        {
          "name": "release",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "commonDir": { "type": "string" }
            },
            "required": ["commonDir"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" }
            },
            "required": ["ok"],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "guards",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "afterApprovalLock",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "commonDir": { "type": "string" }
            },
            "required": ["commonDir"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" },
              "error": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              }
            },
            "required": ["ok", "error"],
            "additionalProperties": false
          }
        },
        {
          "name": "beforeApprovalCommit",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "commonDir": { "type": "string" }
            },
            "required": ["commonDir"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": { "type": "boolean" },
              "error": {
                "oneOf": [
                  { "type": "string" },
                  { "type": "null" }
                ]
              }
            },
            "required": ["ok", "error"],
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
