# Metrics run journal

`src/metrics-hooks.mjs` joins explicit workflow facts to a run mutation without controlling the workflow. Its module function `journalRunMutation` receives the run before and after a mutation, a stable installation source, UTC observation time, transition ID and optional explicit observations. It returns the mutated run with compact immutable event records in `run.metrics.events`. The caller must persist that returned record in the same atomic run write as the ordinary mutation. It must generate the transition ID before that write and reuse it for a replay. The journal is retained after delivery so a later scanner can retry it without relying on the run index.

Preserve a saved completion before a rerun can replace or clear it, and record each new completion or skip with its actual timestamp, step and known area. A changed timestamp or skipped status is a distinct completion; summaries and other run content are never copied. Identical already journaled completion facts need no duplicate. Explicit observations use the supplied kind and data, and support start, outcome, milestone and other capture facts; a caller alone establishes confirmed start, origin, version and candidate. A saved state transition into or out of waiting records its observed time and a bounded reason from the structured wait state. A changed explicitly stored required outcome records the new value. For a cancelled run with the native cancellation record and its time, record once, including after a failed earlier capture, an attempt-scoped `step` with `step: cancel` and `status: done`; a directory name or time alone proves nothing. Never infer a start, candidate, assistance or approval from a run creation, review, test, gate, timestamp or text. Events reuse the run's repository, issue and run ID.

`drainRunJournal` submits the retained events through the injected store and returns `{ok:true,count}` or `{ok:false,error}`. Failure leaves the journal intact and must be exposed as incomplete coverage by the caller; it never creates a workflow gate. Repeated drains retain stable identity and are safe for the store to deduplicate. A failed journal construction must likewise be reported by the integration without stopping the ordinary mutation or claiming complete capture.

## Dependencies

[Metrics capture](metrics-capture.prompt.md) owns valid event fields and privacy filtering; this module calls `captureObservation`. The caller supplies the saved run, stable source and transition identity, observation time and any authoritative explicit facts. The store port supplies `appendEvents({root,events})`.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

The captureObservation call uses the supplied observation as the callee input. The store resource is the actual appendEvents dependency. Atomic persistence of the caller’s returned run and durable delivery remain native integration obligations.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "9e4b91c0c90a695659c53aef490877a6d8a088ff36e6c8c4cd52f8c353f0fab6",
  "entries": [
    {
      "operation": "journalRunMutation",
      "input_schema": {
        "type": "object",
        "properties": {
          "before": {
            "type": "string",
            "description": "JSON text encoding of the saved run before mutation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "after": {
            "type": "string",
            "description": "JSON text encoding of the run after mutation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "source": {
            "type": "string"
          },
          "observedAt": {
            "type": "string"
          },
          "transitionId": {
            "type": "string"
          },
          "observations": {
            "type": "string",
            "description": "JSON text encoding of the explicit observations. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "before",
          "after",
          "source",
          "observedAt",
          "transitionId"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the returned run including metrics.events. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
      "operation": "drainRunJournal",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "string",
            "description": "JSON text encoding of the journaled run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "root": {
            "type": "string"
          }
        },
        "required": [
          "run",
          "root"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the ok/count or ok:false/error drain result. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": [],
      "resource_operations": [
        "store.appendEvents"
      ]
    }
  ],
  "calls": [
    {
      "operation": "captureObservation",
      "target": "prompts/cli/metrics-capture.prompt.md",
      "target_operation": "captureObservation",
      "max_calls": 64
    }
  ],
  "resources": [
    {
      "name": "store",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "appendEvents",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "events": {
                "type": "string",
                "description": "JSON text encoding of the validated metrics events. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
              }
            },
            "required": [
              "root",
              "events"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "value": {
                "type": "string",
                "description": "JSON text encoding of the store reply. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
  "conventions": []
}
```
</details>
