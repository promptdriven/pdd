# service

`service.mjs` exports module function `lookup(service, id)`. Invoke the injected service.lookup callback exactly once with `{id}` and return its `{label}` unchanged. The callback owns network access; the module never calls a network API. Runtime resource service represents this callback. Its fixed test reply is independent of id; exact recorded arguments prove forwarding, not a live service response.

## Domain decisions

The caller supplies the service, so the same application operation can use fixed or recorded replies without contacting a live service. Preserve the exported function's signature, one call and unchanged return value.

When this module is executed directly, provide the native typed-call adapter described by the required contract. Its supported operation and symbol are `lookup`, with input `{id: string}`. Call the same exported application function with an injected `service.lookup` bound to the supplied `fixture.lookup` reply. Return the application's result, updated fixture world and actual per-step call count. Importing the module must not read stdin or start a process. The local native declaration uses command `["node", "examples/fakes/service.mjs"]`; ordinary interpreter checks retain the existing interface without native implementation metadata.

## Dependencies

[Native typed-call contract](../../docs/code-call-adapters.md) is required for native adapter generation and verification. The Runtime `lookup` operation needs only its declared service port; it does not execute the native stdin/stdout bridge.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "275c8076598b5f258e339e34443ec3a2239d0c4fffd8c86772757bf2d9b50827",
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
