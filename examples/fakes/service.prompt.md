# service

`service.mjs` exports module function `lookup(service, id)`. Invoke the injected service.lookup callback exactly once with `{id}` and return its `{label}` unchanged. The callback owns network access; the module never calls a network API. Runtime resource service represents this callback. Its fixed test reply is independent of id; exact recorded arguments prove forwarding, not a live service response.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "3b55ec9fa44868a3e7f4aa30256b4bf9744721488ce16bd12ebc5f93772f012a",
  "entries": [
    {
      "operation": "lookup",
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
              "label": {
                "type": "string"
              }
            },
            "required": [
              "label"
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
