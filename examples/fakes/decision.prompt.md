# decision

`decision.mjs` exports module functions decideReply(reply) and doLookup(service, id). decideReply is pure: reply.available true returns `{label:"Available"}`; false returns `{label:"Unavailable"}`. doLookup calls service.lookup once with `{id}` and applies that same decision to the reply. Runtime operations carry reply or id in objects. No live network access occurs here. The service callback is the sole effect boundary.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f7849644cd8fb3dcba08bbe7bcea51638a96c31d4e9623fa5786f1eefd94ed0c",
  "entries": [
    {
      "operation": "decideReply",
      "input_schema": {
        "type": "object",
        "properties": {
          "reply": {
            "type": "object",
            "properties": {
              "available": {
                "type": "boolean"
              }
            },
            "required": [
              "available"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "reply"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "label": {
            "type": "string"
          }
        },
        "required": [
          "label"
        ],
        "additionalProperties": false
      },
      "errors": []
    },
    {
      "operation": "doLookup",
      "input_schema": {
        "type": "object",
        "properties": {
          "id": {
            "type": "string"
          }
        },
        "required": [
          "id"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "label": {
            "type": "string"
          }
        },
        "required": [
          "label"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "service",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "lookup",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "id": {
                "type": "string"
              }
            },
            "required": [
              "id"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "available": {
                "type": "boolean"
              }
            },
            "required": [
              "available"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 12,
    "max_model_calls": 6
  },
  "conventions": []
}
```
</details>
