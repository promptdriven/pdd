# Metrics capture

`src/metrics-capture.mjs` adapts observed workflow transitions to compact metrics facts. It does not select work, judge evidence, or advance workflows. Module functions `captureObservation` and `backfillRun` return facts; `recordObservation` sends facts through an injected store port. Callers provide event identity, UTC observation time and source identity. Preserve separate observations, including retries and contradictory facts. Backfill is a fallback for saved facts missing from the native journal, as selected by the command; it does not alter source identity or existing observations.

A workflow-created or launch-attempt observation is not a confirmed start. A confirmed start requires an explicit observation and carries its known origin (`autopilot`, `manual`, or `unknown`), launch linkage and installed/candidate versions when supplied. Readiness for independent validation is an explicit milestone with candidate identity, not internal review completion. Validation evidence is distinct from internal steps. Preserve observed outcome (`prompt-only` or `code`) without inferring it from a workflow name. A transition records the supplied step and status before subsequent transitions can overwrite it.

Backfill only fields present in the saved run, using their own timestamps. A saved run's creation time is not proof that its worker started. Missing start, origin, readiness, validation, outcome and intervention coverage remain unknown. Record only approved structured assistance categories and coverage limits; never copy summaries, questions, prompts, chats, approval text, credentials or arbitrary fields. Unknown fields are discarded. Reject invalid identities, times, event types and enumerations. Store failures are returned to the caller without disrupting workflow execution.

## Dependencies

The metrics event and store contract in [metrics model](metrics-model.prompt.md) governs the accepted event envelope and store port. Callers supply the actual workflow records and explicit observations; this module does no I/O except the injected recording port.

The observation envelope uses `schema`, `id`, `repo`, `issue`, `type`, `at`, `observedAt`, `source`, optional `attempt`, and a type-specific `data` object. Backfilled step completions use the saved `done` entry's timestamp and actual done or skipped status, without its summary. The caller supplies a stable prefix for each backfill identity. Reject any observation whose required envelope or type-specific values are invalid; omit invalid optional values rather than publishing arbitrary text. `recordObservation` calls `appendEvents({root, events})` on its injected store and returns `{ok, count}` or `{ok:false, error}`.

Backfill a saved skipped completion as skipped, never as a completed step.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.



<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "6a2bf08162680145dad5536251df581aa035d907067dc3a6bcae8cb57b24d433",
  "entries": [
    {
      "operation": "captureObservation",
      "input_schema": {
        "type": "object",
        "properties": {
          "input": {
            "type": "string",
            "description": "JSON text encoding of the supplied observation envelope. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "input"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the captured facts or rejected observation result. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
      "operation": "backfillRun",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "string",
            "description": "JSON text encoding of the saved run. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          },
          "source": {
            "type": "string"
          },
          "observedAt": {
            "type": "string"
          },
          "idPrefix": {
            "type": "string"
          }
        },
        "required": [
          "run",
          "source",
          "observedAt",
          "idPrefix"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the backfilled facts. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
      "operation": "recordObservation",
      "input_schema": {
        "type": "object",
        "properties": {
          "root": {
            "type": "string"
          },
          "observation": {
            "type": "string",
            "description": "JSON text encoding of the observation. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
          }
        },
        "required": [
          "root",
          "observation"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "value": {
            "type": "string",
            "description": "JSON text encoding of the ok/count or ok:false/error recording result. Decode before applying the public contract; preserve all JSON values and absence inside the encoded value."
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
  "calls": [],
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
