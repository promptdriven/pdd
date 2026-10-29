# database

`database.mjs` exports module function `findBook(db, id)`. It calls the injected SQL connection once with SELECT title FROM books WHERE id = :id and returns `{rows}` in query order. Runtime operation findBook binds the connection as resource db; id is the sole SQL parameter. No host database is opened.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "7aee18ec54202b216cf20e031e15792d18b5dd257b7ab7d3d745b3e9140a9ed8",
  "entries": [
    {
      "operation": "findBook",
      "input_schema": {
        "type": "object",
        "properties": {
          "id": {
            "type": "integer"
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
          "rows": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "title": {
                  "type": "string"
                }
              },
              "required": [
                "title"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "rows"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "db",
      "kind": "sql",
      "access": "read",
      "operations": [
        {
          "name": "find",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "id": {
                "type": "integer"
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
              "rows": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "title": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "title"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "rows"
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
