# Local shared-contract commands

Own `src/contracts.mjs`. Module function
`runContracts({words,options,cwd}, {env,stdout,stderr})` returns an exit code.
`words: []` lists contracts; `words: ['sync']` previews migration;
`options['--write'] === true` applies it. Syntax belongs to the command catalog.
These routes read working files and private local Check history. They never
authenticate, reserve a runtime slot, upload, lint remotely or call a model.

Find the Git root as preflight does. Read Git-visible Markdown/JSON files under
`contracts/`, prompts and discovered scenarios using preflight's bounded native
reads. Do not follow symlinks or secret paths, including during writes. Bind
`access = createStrictSourceAccess(root)` from `src/runtime-preflight.mjs`, using
its [scoped strict source access](runtime-preflight.prompt.md#scoped-strict-source-access)
contract. Use `access.sourceFilePort(visible)` for catalog, prompt, expansion and
original-byte checks, `access.findTests({files})` for discovery, and
`access.captureSource({tests})` for current Story footprints. Fresh write-time
visibility uses the same capability's `sourceFilePort` method. All nested reads
must remain within this boundary; a direct-port wrapper alone is insufficient.
This command owns the no-follow requirement; preflight owns the scoped adapter
and physical source/snapshot checks. Use the
contract-reference module's catalog, expansion, comparison and migration APIs;
this command owns orchestration and presentation, not another resolver.

## Workspace catalog

Use the [workspace authority](runtime-workspace.prompt.md) through the bound strict access capability for catalog/discovery, per-Story footprints, reference ports, preview originals and sync destinations. Filter optional catalog/advice candidates before content reads. Excluded optional data and unavailable sibling footprints stay unavailable/advisory; they cannot create a global refusal. A required selected reference crossing still refuses. Strict no-link reads/writes remain in force; local history association is consumed from its owner without rewriting receipts.


## Listing and freshness

`pdd contracts` lists every catalog record's canonical target and owner file,
its current prompt/test users, and their Stories. Supply current used targets to
the catalog, including seeds and leaf schemas. Include transitive uses; ignore
literal business/expected values. Show unused records with no users. Report
catalog warnings without inventing a record or a user. Skip or warn for an
oversized catalog/discovery-only document before reading its contents; it cannot
abort independent listing, preview or selected good work. Report any affected
record/use or footprint evidence as unavailable rather than complete. Required
selected source retains preflight's bounded safe-read refusals.

Use `readContractHistory` from the runtime client for the most recent actual
Check baseline for each Story. Compare canonical target snapshots, including
removed targets, against that Story's current uses. Say `changed since the last
check` with the affected record identities and `stale: needs a new check` with
the affected Stories. A changed common record affects all its users. Another
record in the same file and another Story in the same batch do not become stale
merely because they shared a file or batch. Other source changes retain ordinary
source freshness behavior. Each Story's current effective footprint is independent
of which other tests were selected: checking one file, all tests for that Story,
or a multi-Story batch must produce the same footprint for unchanged Story
inputs. Account for all discovered tests belonging to that Story and their own
closures, without adding another Story's files. Preflight's
[unavailable-footprint rule](runtime-preflight.prompt.md#source-capture) applies:
report an incomplete current footprint as unavailable with its cause, never as
current or as a selected-source refusal merely because an unselected sibling is
broken. A baseline records a check, not necessarily a pass;
never display a failed result as passing.

With no actual Check baseline or a legacy baseline lacking reference provenance,
show `not checked` or `baseline unavailable`, respectively. Do not invent an old
value or a change. Lint, Try and file previews never advance these baselines.
Current user discovery reflects working files even without history. Unreadable
history is reported as unavailable, never treated as proof of freshness.

## Preview and write

`pdd contracts sync` prints proposed paths, schema locations, canonical targets
and constraint differences. It writes nothing. Ambiguous candidates warn and
skip while independent proposals remain available. Exact copies may migrate as
well as near copies; differing near copies explicitly adopt the canonical shape.

`pdd contracts sync --write` explicitly authorizes applying these proposals.
Before each write require the same safe destination and exact previewed `before`
bytes; a concurrent edit refuses that file without overwriting it. Write the
complete planned bytes into a new exclusive temporary regular file in the safe
destination directory, then atomically rename it into place. Recheck destination
identity, safe ancestors and exact `before` bytes immediately before replacement;
a concurrent content/identity change or symlink refuses without overwriting it
or its target. Failed preparation or replacement leaves the original complete
and removes only this operation's temporary file. Readers see the complete
original or complete replacement, never a truncated/intermediate file. Preserve
unrelated files, prose and unmatched schemas. Write only planned `after` bytes;
report changed paths and skipped/failed paths. Use the planner's draft transition
for edited approved interfaces; never approve, fill hashes or change expectations.
A repeated write with unchanged inputs performs no writes.

Exit 0 for completed listing/preview/write, including advice and ambiguity;
2 for invalid syntax or no repository; 4 for an unsafe/missing required consumer,
reference or refused write; 5 for unavailable local I/O. Keep a finite cause on
stderr; every nonempty output line ends with one newline. No history or source
write happens while merely listing or previewing.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.

- [References](contract-refs.prompt.md): required generation and verification
  context for record, expansion, comparison and migration rules.
- [Preflight](runtime-preflight.prompt.md): required generation and verification
  context for Git discovery, the `createStrictSourceAccess` module export and
  all bound-method inputs/results, and safe native reads.
- [Runtime client](runtime-client.prompt.md#shared-contract-check-history):
  required generation and verification context for the local history API only.
- In Runtime checks, `runContracts({words, options, cwd})` raises `invalid-contracts-input` when `cwd` is empty, resolves the repository root via `git.topLevel({cwd})` and Git-visible paths via `git.listFiles({root})`, reads and writes `<root>/<path>` blobs via `files.stat({path})`, `files.read({path})` and `files.write({path, content})`, reads Check baselines via `history.contractHistory({root})`, writes lines (each ending with `\n`) via `output.stdout({text})` (`<target>  owner: <path>  users: <users|none>  Stories: <stories|none>`, `<target>: changed since the last check (<story>)`, `<story>: stale: needs a new check (last check <state>, <checked_at>)` or `current` or `not checked`, and for `sync`: `<path> <pointer> -> <target>; exact copy`, `Preview: <N> files. Use --write to apply.` or `Updated <path>` and `Sync: <changed> files updated, <failures> refused.`) and `output.stderr({text})`, and returns `{exitCode}`. Physical descriptor-level atomic rename and symlink-race checks stay in `test/contracts-verification.test.mjs`, `test/shared-contracts-native.test.mjs` and `test/shared-contracts.formal.test.mjs`.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "08a761ef159ce6a8a7c20dc7ab4e93467a7add58dd542a70fbce7eed36d0bf06",
  "entries": [
    {
      "operation": "runContracts",
      "input_schema": {
        "type": "object",
        "properties": {
          "words": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "options": {
            "type": "object",
            "properties": {
              "--write": {
                "type": "boolean"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "cwd": {
            "type": "string"
          }
        },
        "required": [
          "words",
          "options",
          "cwd"
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
        "invalid-contracts-input"
      ],
      "resource_operations": [
        "git.topLevel",
        "git.listFiles",
        "files.stat",
        "files.read",
        "files.write",
        "history.contractHistory",
        "output.stdout",
        "output.stderr"
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
              "is_symlink": {
                "type": "boolean"
              },
              "size": {
                "type": "integer",
                "minimum": 0
              }
            },
            "required": [
              "exists",
              "is_symlink",
              "size"
            ],
            "additionalProperties": false
          },
          "name": "stat"
        },
        {
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
          },
          "name": "read"
        },
        {
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
            "properties": {
              "size": {
                "type": "integer",
                "minimum": 0
              }
            },
            "required": [
              "size"
            ],
            "additionalProperties": false
          },
          "name": "write"
        }
      ]
    },
    {
      "name": "git",
      "kind": "port",
      "access": "read",
      "operations": [
        {
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
              "status": {
                "type": "integer"
              },
              "root": {
                "type": "string"
              },
              "stderr": {
                "type": "string"
              }
            },
            "required": [
              "status",
              "root",
              "stderr"
            ],
            "additionalProperties": false
          },
          "name": "topLevel"
        },
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              }
            },
            "required": [
              "root"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "status": {
                "type": "integer"
              },
              "files": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "status",
              "files"
            ],
            "additionalProperties": false
          },
          "name": "listFiles"
        }
      ]
    },
    {
      "name": "history",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              }
            },
            "required": [
              "root"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "stories": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "story_path": {
                      "type": "string"
                    },
                    "baseline": {
                      "type": "string"
                    },
                    "result_state": {
                      "type": "string"
                    },
                    "checked_at": {
                      "type": "string"
                    },
                    "files": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "references": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "kind": {
                            "type": "string"
                          },
                          "target": {
                            "type": "string"
                          },
                          "value_json": {
                            "type": "string"
                          }
                        },
                        "required": [
                          "kind",
                          "target",
                          "value_json"
                        ],
                        "additionalProperties": false
                      }
                    }
                  },
                  "required": [
                    "story_path",
                    "baseline"
                  ],
                  "additionalProperties": false
                }
              },
              "warnings": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "stories",
              "warnings"
            ],
            "additionalProperties": false
          },
          "name": "contractHistory"
        }
      ]
    },
    {
      "name": "output",
      "kind": "port",
      "access": "write",
      "operations": [
        {
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
          },
          "name": "stdout"
        },
        {
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
          },
          "name": "stderr"
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 20,
    "max_model_calls": 10
  },
  "conventions": []
}
```
</details>
