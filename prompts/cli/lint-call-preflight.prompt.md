# Call preflight display

Own `src/lint-call-preflight.mjs`; export pure module function
`describeCallPreflight({test, preflight, context, sourceSha256, requestedCap})`, returning a fresh `{text}`.
This display lets a person inspect the Runtime's call estimate before paid work.
Preserve supplied data without mutation. It never computes a cost or changes a cap.

The input schemas below own the exact server object shape. `selected_cap` is the
chosen total call ceiling, or null when none was selected. `estimated_calls` is
the structural catalog estimate for the test, or null for unknown analysis.
`status` is warning, within-estimate, not-selected or unknown; `complete` states
analysis completeness. `steps` retain scenario order and exact step, entry prompt
and operation identity. `catalog_calls` is that step's canonical catalog cost;
`cumulative_catalog_calls` is the prefix total. Either cost can be null.
`has_external_resources` identifies resource use. `provider_calls` is zero;
`guarantee` and `resource_continuations_included` are false. The context reports
the exact uploaded `source_sha256`, trusted `engine_build` or unknown, selected
cap or null, and configured `max_cap`. The caller supplies its captured `sourceSha256` and selected `requestedCap`
(integer or null). Context is trusted for display only when source_sha256 equals
sourceSha256, engine_build is exactly 40 lowercase hexadecimal characters, both
selected_cap fields equal requestedCap, and context exists. If this association
is missing or inconsistent, use the unavailable heading, omit steps and warning,
and keep the supplied identity line. Never claim a fit from unassociated facts.

Return text with these newline-separated lines, with no trailing newline:

1. With preflight null or untrusted context, `Call preflight (TEST): unavailable; no estimate or cap-fit claim.`
   Otherwise `Call preflight (TEST): STATUS; structural catalog estimate TOTAL calls; selected cap CAP; complete COMPLETE.`
   Substitute the supplied status and boolean, numeric total or `unknown`, and numeric cap or `not selected`.
2. For every supplied step, in order, `  Step ID (ENTRY :: OPERATION): catalog CALLS; cumulative CUMULATIVE; external resources BOOLEAN.`
   Substitute `unknown` for either null cost. Null preflight or untrusted context has no steps.
3. With context, `  Source SOURCE; engine ENGINE; configured maximum MAX.`
   Without it, `  Source and engine identity unavailable.`
4. Only for trusted supplied warning status, `  Warning: the structural estimate exceeds the selected cap; the cap is unchanged.`
5. Always `  Advisory only: no guarantee of actual calls or completion; resource continuations are not included. Lint uses 0 AI calls.`

TOTAL and step costs come only from the server. Incomplete and unknown reports
keep unknown values. Within-estimate never becomes a promise of fit or completion.
Text values retain their bytes; this helper adds no terminal styling or effects.

## Dependencies

None. This pure formatter uses only its explicit input and standard string formatting.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "2d650d58934e1160ed534f7af5cb32b7510da8e69b4e338c1294dc44f237f443",
  "entries": [
    {
      "operation": "describeCallPreflight",
      "input_schema": {
        "type": "object",
        "properties": {
          "test": {
            "type": "string"
          },
          "preflight": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "selected_cap": {
                    "oneOf": [
                      {
                        "type": "integer",
                        "minimum": 1,
                        "maximum": 1000
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "estimate_kind": {
                    "type": "string",
                    "enum": [
                      "structural-catalog"
                    ]
                  },
                  "estimated_calls": {
                    "oneOf": [
                      {
                        "type": "integer",
                        "minimum": 0
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "status": {
                    "type": "string",
                    "enum": [
                      "warning",
                      "within-estimate",
                      "not-selected",
                      "unknown"
                    ]
                  },
                  "complete": {
                    "type": "boolean"
                  },
                  "provider_calls": {
                    "type": "integer",
                    "const": 0
                  },
                  "guarantee": {
                    "type": "boolean",
                    "const": false
                  },
                  "resource_continuations_included": {
                    "type": "boolean",
                    "const": false
                  },
                  "steps": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "step_id": {
                          "type": "string"
                        },
                        "entry_path": {
                          "type": "string"
                        },
                        "operation": {
                          "type": "string"
                        },
                        "catalog_calls": {
                          "oneOf": [
                            {
                              "type": "integer",
                              "minimum": 0
                            },
                            {
                              "type": "null"
                            }
                          ]
                        },
                        "has_external_resources": {
                          "type": "boolean"
                        },
                        "cumulative_catalog_calls": {
                          "oneOf": [
                            {
                              "type": "integer",
                              "minimum": 0
                            },
                            {
                              "type": "null"
                            }
                          ]
                        }
                      },
                      "required": [
                        "step_id",
                        "entry_path",
                        "operation",
                        "catalog_calls",
                        "has_external_resources",
                        "cumulative_catalog_calls"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "selected_cap",
                  "estimate_kind",
                  "estimated_calls",
                  "status",
                  "complete",
                  "provider_calls",
                  "guarantee",
                  "resource_continuations_included",
                  "steps"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "context": {
            "oneOf": [
              {
                "type": "object",
                "properties": {
                  "source_sha256": {
                    "type": "string"
                  },
                  "engine_build": {
                    "type": "string"
                  },
                  "selected_cap": {
                    "oneOf": [
                      {
                        "type": "integer",
                        "minimum": 1,
                        "maximum": 1000
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "max_cap": {
                    "type": "integer",
                    "minimum": 1,
                    "maximum": 1000
                  }
                },
                "required": [
                  "source_sha256",
                  "engine_build",
                  "selected_cap",
                  "max_cap"
                ],
                "additionalProperties": false
              },
              {
                "type": "null"
              }
            ]
          },
          "sourceSha256": {
            "type": "string"
          },
          "requestedCap": {
            "oneOf": [
              {
                "type": "integer",
                "minimum": 1,
                "maximum": 1000
              },
              {
                "type": "null"
              }
            ]
          }
        },
        "required": [
          "test",
          "preflight",
          "context",
          "sourceSha256",
          "requestedCap"
        ],
        "additionalProperties": false
      },
      "result_schema": {
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
      "errors": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 12,
    "max_model_calls": 4
  },
  "conventions": []
}
```
</details>
