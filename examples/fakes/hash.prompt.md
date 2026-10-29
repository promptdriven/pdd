# hash

`hash.mjs` exports module function `fingerprint(compute, text)`. Return `{value}` from exactly one compute.hash_utf8 call with the unchanged text. This computes lowercase hexadecimal SHA-256 of exact UTF-8 bytes, with no trimming, newline insertion or JSON serialization.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "f2075e27c24ac14795e145a9add6390d0cfb639e2c5bf86dbecb6aa7ebafee66",
  "entries": [
    {
      "operation": "fingerprint",
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
          "value": {
            "type": "string"
          }
        },
        "required": [
          "value"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
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
