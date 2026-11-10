# Metrics capture gap fallback

`src/metrics-gap.mjs` exports `recordCaptureGap({commonDir, repo, issue, at})`, which records an incomplete coverage observation for a repository issue when ordinary metrics identity or delivery fails. Store only the lowercase repository `owner/repo`, positive integer issue number, ISO-8601 UTC observation time `at` (`new Date(at).toISOString()`), and generated event identity `id` from `ids.randomUUID`: `{schema: "pdd.metrics.event.v1", id: "gap:<id>", repo, issue, type: "coverage", at, observedAt: at, source: "gap:<id>", data: {complete: false}}`; do not store paths, text, credentials or conversation. Write a new private file `<commonDir>/pdd/metrics-gaps/<id>.json`, sync its bytes, atomically publish it and sync the directory, returning `{file, event}`. Raise `invalid-gap-observation` before storage access when `commonDir` is blank, `repo` is not `owner/repo`, `issue` is not a positive integer or `at` is not a valid timestamp. Raise `storage-unavailable` to the caller if `commonDir` is missing, is a symlink, or cannot store the gap file; callers warn and continue their ordinary operation. The metrics command replays valid saved gaps. This fallback is evidence of missing coverage, never a workflow gate.

## Dependencies

Bind `commonDir` inspection and gap-file persistence through `files.stat` and `files.write`, and UUID allocation through `ids.randomUUID`. Exclusive temporary-file creation (`wx` mode `0600`), `fsync`, atomic `rename` and parent-directory sync remain native obligations (`test/metrics-workflow-storage.integration.test.mjs`, `test/metrics-selector.integration.test.mjs`).

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "75da0617056efe86d4f5e69bbac08673a0170182737907a0b86a44824e7a5a6c",
  "entries": [
    {
      "operation": "recordCaptureGap",
      "input_schema": {
        "type": "object",
        "properties": {
          "commonDir": { "type": "string" },
          "repo": { "type": "string" },
          "issue": { "type": "integer" },
          "at": { "type": "string" }
        },
        "required": ["commonDir", "repo", "issue", "at"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "file": { "type": "string" },
          "event": {
            "type": "object",
            "properties": {
              "schema": { "type": "string", "enum": ["pdd.metrics.event.v1"] },
              "id": { "type": "string" },
              "repo": { "type": "string" },
              "issue": { "type": "integer" },
              "type": { "type": "string", "enum": ["coverage"] },
              "at": { "type": "string" },
              "observedAt": { "type": "string" },
              "source": { "type": "string" },
              "data": {
                "type": "object",
                "properties": {
                  "complete": { "type": "boolean" }
                },
                "required": ["complete"],
                "additionalProperties": false
              }
            },
            "required": ["schema", "id", "repo", "issue", "type", "at", "observedAt", "source", "data"],
            "additionalProperties": false
          }
        },
        "required": ["file", "event"],
        "additionalProperties": false
      },
      "errors": ["invalid-gap-observation", "storage-unavailable"],
      "resource_operations": ["files.stat", "files.write", "ids.randomUUID"]
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
          "name": "stat",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" }
            },
            "required": ["path"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exists": { "type": "boolean" },
              "size": { "type": "integer", "minimum": 0 },
              "is_symlink": { "type": "boolean" }
            },
            "required": ["exists", "size", "is_symlink"],
            "additionalProperties": false
          }
        },
        {
          "name": "write",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": { "type": "string" },
              "content": { "type": "string" }
            },
            "required": ["path", "content"],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "ids",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "randomUUID",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {},
            "required": [],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "id": { "type": "string" }
            },
            "required": ["id"],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 16,
    "max_model_calls": 8
  },
  "conventions": []
}
```
</details>
