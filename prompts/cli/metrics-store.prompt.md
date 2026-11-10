# Compact metrics ledger

`src/metrics-store.mjs` exports module functions `appendEvents({root, events})`, `readEvents({root})`, `exportMetrics({root, metadata})`, and `importMetrics({root, bundle})`. The ledger retains compact event facts beneath the repository git common PDD state independently of the disposable 200-run index and overwritten workflow status. New records are durable, and backfill records only facts actually evidenced. Preserve these interfaces and effects; storage representation is free.

The [calculator event contract](metrics-model.prompt.md) owns event identity and facts. Identical events imported repeatedly do not inflate the ledger. Conflicting payloads with the same source/id remain visible, rather than choosing a successful result. Validate an entire import and its definition/schema compatibility before writing; reject malformed or incompatible bundles without a partial import. Concurrent append/import must not lose events. An export carries schema and metric-definition versions, repository, export time, timezone, pseudonymous installation/source identity and coverage bounds. A missing machine is a coverage gap, not an empty contributor. Explicit export contains no credentials, prompts, raw chats, raw issue bodies or local paths.

The optional second `ports` argument can supply `ledger.read({root})` and `ledger.write({root, events, sources, snapshots})`; the first returns `{events, sources, snapshots}`, and the second atomically persists the supplied records. `readEvents`, `appendEvents`, and `importMetrics` return `{events, sources, snapshots}`. `exportMetrics` returns `{bundle}`. Metadata supplies `repo` and `timezone`, and may supply `exportedAt`, `cliVersion`, and coverage bounds; `installation.read({root})` supplies `{source, captureStartedAt}`. Failures propagate without claiming success: `readEvents` raises `invalid-ledger`, `appendEvents` raises `invalid-metrics-event`, `exportMetrics` raises `invalid-export-metadata`, `importMetrics` raises `invalid-metrics-bundle`, and `validateSnapshot({snapshot, repository})` returns `{valid: true}` or raises `invalid-selector-snapshot`. Native filesystem locking, permissions and crash behavior remain native obligations (`test/metrics-store.test.mjs`).

## Dependencies

[Metrics calculator](metrics-model.prompt.md): required for event identity and facts in authoring, generation and native testing.


Bundles may include `sources`, an array of participating source metadata with source, capture start, coverage, version, definition, export time and timezone. Preserve these records over repeated imports and exports, validating them before any write; older bundles without the array remain readable. The top-level bundle source and each nested source use the same identifier contract before any write. Reject arbitrary prose and local paths in identifiers and facts. Evidence links may have public GitHub comment fragments but no credentials or query strings.

Checker family and checker mode are retained as bounded categorical facts for cross-source agreement. Identifiers and categorical facts use bounded token syntax; selection reasons use bounded category tokens or the fixed unavailable-selector message. A reviewer may use the documented public-comment identity description. Reject URLs targeting localhost or private IP addresses and never accept query strings.

Allow public GitHub check-run references and safe CI check names as reason values. Do not retain raw comment text or private names.

Bundles retain complete selector snapshot headers and member selection events, including empty snapshots, so imports preserve observed membership and its time. Validate repository, identity and event consistency before writing.

Every new export declares `scope: "all-retained-repo-events"`: its events and snapshots are the retained records for the exported repository, without a report date or snapshot filter. Preserve the scope of each imported source through later exports. A v1 bundle or nested source without scope remains readable and its scope remains unknown; do not infer it from a later export. When present, scope must be this supported value. Validate top-level and nested scope before any import write.

Module function `validateSnapshot(snapshot, repository)` is the existing canonical selector-snapshot validator exposed for read-only consumers. With a canonical repository name it validates the complete header, permitted event envelope/data fields and values, timestamp/source bindings, selection type/snapshot/repository consistency and unique issue membership using the same validation as bundle import/export. It returns undefined on success and throws on invalid data, without I/O, mutation, storage, process or network effects. Consumers must not substitute a partial second classifier.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "bea433a73cda538191de18f220fd38d1a53695438d1939b42d4fa448bb7319d2",
  "entries": [
    {
      "operation": "readEvents",
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
          "events": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "issue": { "type": "integer" },
                "type": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "data": {
                  "type": "object",
                  "properties": {
                    "origin": { "type": "string" },
                    "complete": { "type": "boolean" }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
              "additionalProperties": false
            }
          },
          "sources": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "source": { "type": "string" },
                "scope": { "type": "string" },
                "captureStartedAt": { "type": "string" },
                "exportedAt": { "type": "string" },
                "timezone": { "type": "string" },
                "cliVersion": { "type": "string" },
                "metricDefinitionVersion": { "type": "string" }
              },
              "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
              "additionalProperties": false
            }
          },
          "snapshots": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "issues": {
                  "type": "array",
                  "items": { "type": "integer" }
                }
              },
              "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
              "additionalProperties": false
            }
          }
        },
        "required": ["events", "sources", "snapshots"],
        "additionalProperties": false
      },
      "errors": ["invalid-ledger"],
      "resource_operations": ["ledger.read"]
    },
    {
      "operation": "appendEvents",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": { "type": "string" },
          "events": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "issue": { "type": "integer" },
                "type": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "data": {
                  "type": "object",
                  "properties": {
                    "origin": { "type": "string" },
                    "complete": { "type": "boolean" },
                    "evidence": { "type": "string" }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
              "additionalProperties": false
            }
          }
        },
        "required": ["root", "events"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "events": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "issue": { "type": "integer" },
                "type": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "data": {
                  "type": "object",
                  "properties": {
                    "origin": { "type": "string" },
                    "complete": { "type": "boolean" },
                    "evidence": { "type": "string" }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
              "additionalProperties": false
            }
          },
          "sources": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "source": { "type": "string" },
                "scope": { "type": "string" },
                "captureStartedAt": { "type": "string" },
                "exportedAt": { "type": "string" },
                "timezone": { "type": "string" },
                "cliVersion": { "type": "string" },
                "metricDefinitionVersion": { "type": "string" }
              },
              "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
              "additionalProperties": false
            }
          },
          "snapshots": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "issues": {
                  "type": "array",
                  "items": { "type": "integer" }
                }
              },
              "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
              "additionalProperties": false
            }
          }
        },
        "required": ["events", "sources", "snapshots"],
        "additionalProperties": false
      },
      "errors": ["invalid-metrics-event"],
      "resource_operations": ["ledger.read", "ledger.write"]
    },
    {
      "operation": "exportMetrics",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": { "type": "string" },
          "metadata": {
            "type": "object",
            "properties": {
              "repo": { "type": "string" },
              "timezone": { "type": "string" },
              "exportedAt": { "type": "string" },
              "cliVersion": { "type": "string" }
            },
            "required": ["repo", "timezone"],
            "additionalProperties": false
          }
        },
        "required": ["root", "metadata"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "bundle": {
            "type": "object",
            "properties": {
              "schema": { "type": "string" },
              "metricDefinitionVersion": { "type": "string" },
              "scope": { "type": "string" },
              "repo": { "type": "string" },
              "exportedAt": { "type": "string" },
              "timezone": { "type": "string" },
              "source": { "type": "string" },
              "captureStartedAt": { "type": "string" },
              "cliVersion": { "type": "string" },
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "data": {
                      "type": "object",
                      "properties": {
                        "origin": { "type": "string" },
                        "complete": { "type": "boolean" }
                      },
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
                  "additionalProperties": false
                }
              },
              "sources": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "source": { "type": "string" },
                    "scope": { "type": "string" },
                    "captureStartedAt": { "type": "string" },
                    "exportedAt": { "type": "string" },
                    "timezone": { "type": "string" },
                    "cliVersion": { "type": "string" },
                    "metricDefinitionVersion": { "type": "string" }
                  },
                  "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
                  "additionalProperties": false
                }
              },
              "snapshots": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "issues": {
                      "type": "array",
                      "items": { "type": "integer" }
                    }
                  },
                  "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "schema",
              "metricDefinitionVersion",
              "scope",
              "repo",
              "exportedAt",
              "timezone",
              "source",
              "captureStartedAt",
              "cliVersion",
              "events",
              "sources",
              "snapshots"
            ],
            "additionalProperties": false
          }
        },
        "required": ["bundle"],
        "additionalProperties": false
      },
      "errors": ["invalid-export-metadata"],
      "resource_operations": ["ledger.read", "installation.read"]
    },
    {
      "operation": "importMetrics",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": { "type": "string" },
          "bundle": {
            "type": "object",
            "properties": {
              "schema": { "type": "string" },
              "metricDefinitionVersion": { "type": "string" },
              "scope": { "type": "string" },
              "repo": { "type": "string" },
              "exportedAt": { "type": "string" },
              "timezone": { "type": "string" },
              "source": { "type": "string" },
              "captureStartedAt": { "type": "string" },
              "cliVersion": { "type": "string" },
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "data": {
                      "type": "object",
                      "properties": {
                        "origin": { "type": "string" },
                        "complete": { "type": "boolean" }
                      },
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
                  "additionalProperties": false
                }
              },
              "sources": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "source": { "type": "string" },
                    "scope": { "type": "string" },
                    "captureStartedAt": { "type": "string" },
                    "exportedAt": { "type": "string" },
                    "timezone": { "type": "string" },
                    "cliVersion": { "type": "string" },
                    "metricDefinitionVersion": { "type": "string" }
                  },
                  "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
                  "additionalProperties": false
                }
              },
              "snapshots": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "issues": {
                      "type": "array",
                      "items": { "type": "integer" }
                    }
                  },
                  "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "schema",
              "metricDefinitionVersion",
              "repo",
              "exportedAt",
              "timezone",
              "source",
              "captureStartedAt",
              "cliVersion",
              "events"
            ],
            "additionalProperties": false
          }
        },
        "required": ["root", "bundle"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "events": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "issue": { "type": "integer" },
                "type": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "data": {
                  "type": "object",
                  "properties": {
                    "origin": { "type": "string" },
                    "complete": { "type": "boolean" }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
              "additionalProperties": false
            }
          },
          "sources": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "source": { "type": "string" },
                "scope": { "type": "string" },
                "captureStartedAt": { "type": "string" },
                "exportedAt": { "type": "string" },
                "timezone": { "type": "string" },
                "cliVersion": { "type": "string" },
                "metricDefinitionVersion": { "type": "string" }
              },
              "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
              "additionalProperties": false
            }
          },
          "snapshots": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": { "type": "string" },
                "id": { "type": "string" },
                "repo": { "type": "string" },
                "at": { "type": "string" },
                "observedAt": { "type": "string" },
                "source": { "type": "string" },
                "issues": {
                  "type": "array",
                  "items": { "type": "integer" }
                }
              },
              "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
              "additionalProperties": false
            }
          }
        },
        "required": ["events", "sources", "snapshots"],
        "additionalProperties": false
      },
      "errors": ["invalid-metrics-bundle"],
      "resource_operations": ["ledger.read", "ledger.write"]
    },
    {
      "operation": "validateSnapshot",
      "input_schema": {
        "type": "object",
        "properties": {
          "snapshot": {
            "type": "object",
            "properties": {
              "schema": { "type": "string" },
              "id": { "type": "string" },
              "repo": { "type": "string" },
              "at": { "type": "string" },
              "observedAt": { "type": "string" },
              "source": { "type": "string" },
              "issues": {
                "type": "array",
                "items": { "type": "integer" }
              }
            },
            "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
            "additionalProperties": false
          },
          "repository": { "type": "string" }
        },
        "required": ["snapshot", "repository"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "valid": { "type": "boolean" }
        },
        "required": ["valid"],
        "additionalProperties": false
      },
      "errors": ["invalid-selector-snapshot"],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "ledger",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "read",
          "access": "write",
          "arguments_schema": {
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
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "data": {
                      "type": "object",
                      "properties": {
                        "origin": { "type": "string" },
                        "complete": { "type": "boolean" }
                      },
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
                  "additionalProperties": false
                }
              },
              "sources": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "source": { "type": "string" },
                    "scope": { "type": "string" },
                    "captureStartedAt": { "type": "string" },
                    "exportedAt": { "type": "string" },
                    "timezone": { "type": "string" },
                    "cliVersion": { "type": "string" },
                    "metricDefinitionVersion": { "type": "string" }
                  },
                  "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
                  "additionalProperties": false
                }
              },
              "snapshots": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "issues": {
                      "type": "array",
                      "items": { "type": "integer" }
                    }
                  },
                  "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["events", "sources", "snapshots"],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": { "type": "string" },
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "issue": { "type": "integer" },
                    "type": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "data": {
                      "type": "object",
                      "properties": {
                        "origin": { "type": "string" },
                        "complete": { "type": "boolean" }
                      },
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
                  "additionalProperties": false
                }
              },
              "sources": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "source": { "type": "string" },
                    "scope": { "type": "string" },
                    "captureStartedAt": { "type": "string" },
                    "exportedAt": { "type": "string" },
                    "timezone": { "type": "string" },
                    "cliVersion": { "type": "string" },
                    "metricDefinitionVersion": { "type": "string" }
                  },
                  "required": ["source", "captureStartedAt", "exportedAt", "timezone", "cliVersion", "metricDefinitionVersion"],
                  "additionalProperties": false
                }
              },
              "snapshots": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": { "type": "string" },
                    "id": { "type": "string" },
                    "repo": { "type": "string" },
                    "at": { "type": "string" },
                    "observedAt": { "type": "string" },
                    "source": { "type": "string" },
                    "issues": {
                      "type": "array",
                      "items": { "type": "integer" }
                    }
                  },
                  "required": ["schema", "id", "repo", "at", "observedAt", "source", "issues"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["root", "events", "sources", "snapshots"],
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
      "name": "installation",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "read",
          "access": "write",
          "arguments_schema": {
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
              "source": { "type": "string" },
              "captureStartedAt": { "type": "string" }
            },
            "required": ["source", "captureStartedAt"],
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
