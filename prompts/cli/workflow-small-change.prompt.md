# Small-change request evidence

Own `src/workflow-small-change.mjs`. Preserve every issue request through a
small-change plan, publication and independent review. This module checks
structured evidence, not the truth of agent claims or arbitrary English intent.

`readSmallChangeChecklist(run)` reads only `<runDir>/small-change-checklist.json`.
Use a regular file, at most 1 MiB. The record is `{schema_version:
"pdd.small-change-checklist.v1", run_id, source:{kind:"git-content-v1",sha256},
items}`. `run_id` must match. The source fingerprint must match the current
Git-visible content. Missing, malformed and stale evidence returns `{status,
items:[],mustFix:[{id,code}]}` with the corresponding status and code. A valid
record returns `{status:"recorded",items,mustFix}`. Keep every item in order.
Each item has unique nonblank `id`, `request`, `source` (issue or trusted comment
URL), `quote` (the exact request excerpt), `state` (`pending`, `done`, `excluded`).
Done needs nonblank `evidence`. Excluded needs `exclusion:{reason,quote}`;
that quote must support exclusion in the issue itself. No plan-only exemption.
Missing completion evidence is a must-fix, not a schema error. Empty inventories
are malformed. Do not truncate an inventory to make it pass.

`reviewSmallChangeChecklist(checklist, requests)` returns must-fix objects
`{id,code}`. `requests` is an independent issue-derived inventory, with the same
id/request/source/quote fields and optional `exclusion_quote`: the exact issue
text the checker judged authorizes exclusion. Match by source, request and quote,
not by the builder's id. Missing requests give `missing-request`; extra checklist
items give no coverage of another request. Validate every checklist row by its
own unique id, including extra rows and rows with identical request/source/quote.
A completed row cannot supply another row's state, evidence or exclusion.
Pending items give `pending-request`;
done without evidence gives `missing-evidence`; exclusions without a reason and
an exact match to a matching independent request's `exclusion_quote` give
`unsupported-exclusion`. Report completion findings with the checklist row's id;
report missing requests with the independent request's id.
The reader uses the same completion checks without an independent inventory;
it does not claim semantic completeness or authorize an exclusion. The checker
must derive requests from the full issue and trusted follow-ups, never the plan.

## Dependencies

- [Replay evidence](workflow-replay.prompt.md): required fingerprint contract
  `sourceFingerprint` for current Git-visible content.
- In Runtime checks, `files.stat({path})` and `files.read({path})` inspect `<runDir>/small-change-checklist.json`, and `replay.sourceFingerprint({root})` returns `{kind, sha256}` for `<root>`. `readSmallChangeChecklist({run})` returns `{status, items, mustFix}` (`mustFix` is `[{id:"checklist", code:"missing-checklist"|"malformed-checklist"|"stale-checklist"}]` when `status` is `missing`, `malformed` or `stale`) and fails with `invalid_checklist_run` when `run.runId`, `run.runDir` or `run.root` is empty; `reviewSmallChangeChecklist({checklist, requests})` returns `{findings}` and fails with `invalid_request_inventory` when `requests` is empty. Native Git index enumeration and disposable filesystem checks stay in `test/workflow-small-change-scope.test.mjs`.

Small-change checklist and Formal check facts remain in detailed text status and JSON run rows. Preserve compact list/all text rows; these views keep existing Runtime coverage lines but do not add the detailed small-change evidence block. The saved evidence remains available through the run detail and JSON.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f6ea0715cd45e75bef520c266849bf8c105ab45011cb0cedf479ae9c31f04e1e",
  "entries": [
    {
      "operation": "readSmallChangeChecklist",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "runDir": {
                "type": "string"
              },
              "root": {
                "type": "string"
              }
            },
            "required": [
              "runId",
              "runDir",
              "root"
            ],
            "additionalProperties": false
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
          "status": {
            "type": "string",
            "enum": [
              "recorded",
              "missing",
              "malformed",
              "stale"
            ]
          },
          "items": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "request": {
                  "type": "string"
                },
                "source": {
                  "type": "string"
                },
                "quote": {
                  "type": "string"
                },
                "state": {
                  "type": "string",
                  "enum": [
                    "pending",
                    "done",
                    "excluded"
                  ]
                },
                "evidence": {
                  "type": "string"
                },
                "exclusion": {
                  "type": "object",
                  "properties": {
                    "reason": {
                      "type": "string"
                    },
                    "quote": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "reason",
                    "quote"
                  ],
                  "additionalProperties": false
                }
              },
              "required": [
                "id",
                "request",
                "source",
                "quote",
                "state"
              ],
              "additionalProperties": false
            }
          },
          "mustFix": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "code": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "code"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "status",
          "items",
          "mustFix"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_checklist_run"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "replay.sourceFingerprint"
      ]
    },
    {
      "operation": "reviewSmallChangeChecklist",
      "input_schema": {
        "type": "object",
        "properties": {
          "checklist": {
            "type": "object",
            "properties": {
              "status": {
                "type": "string",
                "enum": [
                  "recorded",
                  "missing",
                  "malformed",
                  "stale"
                ]
              },
              "items": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": {
                      "type": "string"
                    },
                    "request": {
                      "type": "string"
                    },
                    "source": {
                      "type": "string"
                    },
                    "quote": {
                      "type": "string"
                    },
                    "state": {
                      "type": "string",
                      "enum": [
                        "pending",
                        "done",
                        "excluded"
                      ]
                    },
                    "evidence": {
                      "type": "string"
                    },
                    "exclusion": {
                      "type": "object",
                      "properties": {
                        "reason": {
                          "type": "string"
                        },
                        "quote": {
                          "type": "string"
                        }
                      },
                      "required": [
                        "reason",
                        "quote"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "id",
                    "request",
                    "source",
                    "quote",
                    "state"
                  ],
                  "additionalProperties": false
                }
              },
              "mustFix": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": {
                      "type": "string"
                    },
                    "code": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "id",
                    "code"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "status",
              "items",
              "mustFix"
            ],
            "additionalProperties": false
          },
          "requests": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "request": {
                  "type": "string"
                },
                "source": {
                  "type": "string"
                },
                "quote": {
                  "type": "string"
                },
                "exclusion_quote": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "request",
                "source",
                "quote"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "checklist",
          "requests"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "findings": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "id": {
                  "type": "string"
                },
                "code": {
                  "type": "string"
                }
              },
              "required": [
                "id",
                "code"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "findings"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid_request_inventory"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "blob",
      "access": "read",
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
        }
      ]
    },
    {
      "name": "replay",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "sourceFingerprint",
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
              "kind": {
                "type": "string"
              },
              "sha256": {
                "type": "string"
              }
            },
            "required": [
              "kind",
              "sha256"
            ],
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
