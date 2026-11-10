# Local screen comparison

Own `src/screen-compare.mjs`. Its module function `compareScreen({url, drawingPath, cwd, chromePath}, ports = {})` renders a real page and its `.ui.svg` reference in headless Chrome/Chromium, then returns `{drawing, url, viewport, rows, passed}`. `viewport` has CSS-pixel `width` and `height`. Each row has `{part, kind, expected, actual, status}`; `kind` is `id` or `text`, status is `pass`, `missing`, `hidden`, `region` or `order`. `expected` and `actual` are concise readable observations. `passed` is true only if every required row passes. The module function `formatScreenComparison(report)` returns a Markdown `Screen vs drawing` table and a pass/fail summary. Render supplied content literally: escape Markdown backslashes, punctuation and HTML-special characters, and flatten line breaks so content cannot alter the table or introduce links/HTML. No AI, PDD runtime, gh authentication or saved check batch is involved.

## Reference and browser

Resolve `drawingPath` from `cwd`; require a readable regular `.ui.svg` file. Accept only an http/https page URL without embedded credentials. A missing drawing, invalid SVG, unsafe reference, failed navigation or browser failure is an explicit error, never an empty passing comparison. Ignore valid XML comments and treat CDATA as literal text; reject malformed or nested comments rather than removing delimiters and reinterpreting their contents. Browser executable selection is explicit `chromePath`, then `PDD_CHROME_PATH`, then an installed Chrome/Chromium executable. `ports` may replace browser execution/environment for ordinary local tests. Do not require a private dependency or downloaded browser. Explain how to set `PDD_CHROME_PATH` when no browser exists.

Set the browser viewport from the drawing's positive viewBox width/height, falling back to positive numeric width/height when there is no viewBox. Reject a missing/invalid viewport; keep any nonzero viewBox origin accounted for in reference geometry. Render both the drawing and page with the same CSS-pixel viewport and device scale 1. Wait for page load and fonts, with a finite timeout; clean up the browser and temporary profile on success and every error. Read transformed bounding boxes from the rendered SVG, including nested groups and text, rather than assuming raw x/y attributes describe the screen. Never execute reference scripts or load external SVG resources; reject such reference content with a clear error.

## Comparison

Every visible reference id and every visible `<text>` label is required, including numeric labels and duplicates. Metadata (`title`, `desc`, `defs`), hidden elements and context-only subtrees (`data-context-only="true"` or class `context-only`) are excluded. The reference must contain at least one required part; malformed or unsupported reference content must not silently turn into a passing empty result.

An id maps to the page element with that exact unique id. Duplicate page/reference ids fail with a clear diagnostic. Text maps by exact whitespace-normalized visible text, preserving case. When a reference label has a uniquely matched enclosing id, only that page element's own text or descendant occurrences may satisfy it. If none exist there, report `missing`, even when the same label appears elsewhere; never fall back to outside text. Without a matched enclosing id, text matching remains global. Consume distinct text occurrences once; a single label cannot satisfy repeated reference labels. Page text may be in ordinary DOM elements or form controls. Only literal displayed control labels count: text-like input values, textarea values, selected option labels and explicit button/submit/reset labels. Password secrets and checkbox/radio, color, range, image, file or hidden input values are not visible labels. Native date/month/week/time/datetime-local values may be formatted; their stored strings must not be assumed displayed. A native control may satisfy its visible id without supplying a literal text match. Never include private input values in reports or diagnostics.

A hidden label, accessibility name, script text or offscreen copy cannot satisfy a visible reference label. Visible means rendered, effective nontransparent paint, nonzero bounds and intersecting the viewport; report a matching hidden/outside element as `hidden` and an absent element as `missing`. Text visibility follows effective glyph paint, including text-fill overrides, rather than CSS color alone; the same rule applies when text supplies an id's only paint. Masked text cannot supply its underlying literal. If text stroke/shadow, masking, formatted native controls or applied clipping/filter effects cannot be established, return an explicit unsupported-visibility error rather than a pass. Ordinary visible text (including SVG textPath ids), safe local SVG gradient paint and structural regions with visible painted descendants remain supported. Distinguish structural SVG containers and unapplied resource/metadata nodes from unsupported painted elements. If nontransparent paint or geometry cannot be established, including stroked SVG geometry with zero width or height in its geometric bounds, return an explicit unsupported-visibility error; never silently omit that required reference id or accept an unsupported page element as its match. Apply this guard after hidden/transparent exclusion so those reference parts stay excluded.

Compare matched parts' normalized center coordinates: each axis may differ by at most 0.15 of the viewport dimension. Outside this tolerance is `region`. Preserve the spatial order of nonnested parts whose reference bounds are separated vertically or horizontally by more than 2 CSS pixels; overlapping/nested parts impose no extra order. Compare visual geometry, never SVG source order or DOM/focus order. An inversion gives an `order` failure naming the other part. Presence is not enough: an id with unrelated content cannot hide missing text rows. A missing score box, seed box or READY bar must fail even if some score/seed words appear elsewhere.

Keep one table row per required id/text occurrence in stable reference order, including failed parts. Each row's `part` is `#<id>` for an `id` part or `"<text>"` for a `text` part; normalized center coordinates `(cx, cy)` round `((x + width / 2) / viewportDimension)` to two decimal places (for example `0.50`), with `expected` formatted as `<part> (<cx>, <cy>)` and `actual` formatted as `<part> at (<cx>, <cy>)` when visible, `"not found"` when `missing`, `"hidden or outside viewport"` when `hidden`, or `<part> at (<cx>, <cy>), order inverted with <otherPart>` when `order`. State viewport and reference path in the report (`# Screen vs drawing`, `- Drawing: \`<drawing>\``, `- URL: \`<url>\``, `- Viewport: \`<width>x<height>\``, `- Verdict: PASS` or `FAIL`, followed by the `| Part | Kind | Expected | Actual | Status |` Markdown table). This checks parts, text, approximate regions and order; it does not certify colors, typography or pixel equivalence. The caller must arrange the named reference state and dynamic values before invoking it; never drop unmatched words or numbers as “samples” to manufacture a pass.

## Dependencies

- [Screen rules](../../RUNBOOK.md#13-give-your-app-a-screen-app-map): generation and verification context.
- In Runtime checks, `compareScreen` validates `url` (raising `invalid-screen-url` for a non-http/https URL or embedded credentials), resolves `<cwd>/<drawingPath>` and reads it via `files.stat({path})` and `files.read({path})` (raising `drawing-unreadable` when the path does not end with `.ui.svg`, is missing or is a symlink, and `unsafe-reference-svg` when the SVG has malformed comments, DOCTYPE/ENTITY declarations or `<script>`/`<foreignObject>`/`<iframe>`/`<object>`/`<embed>` elements), then calls `browser.render({url, drawing, chromePath})` to obtain `{viewport, reference, actual}` part boxes and computes `{drawing, url, viewport, rows, passed}` (raising `empty-reference-parts` when no visible reference part exists and `duplicate-screen-id` on duplicate visible ids). `formatScreenComparison({report})` returns `{markdown}` and raises `invalid-comparison-report` when `report.viewport` or `report.rows` is missing. Real headless Chrome execution and DOM paint extraction stay in `test/screen-compare.test.mjs`.

## Caller navigation

[Check](runtime-client.prompt.md) owns CLI routing, output and exit codes.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "cf868823300ff4483539ed49f7b19d5de2cfc19829de8815f3345e6f195d068e",
  "entries": [
    {
      "operation": "compareScreen",
      "input_schema": {
        "type": "object",
        "properties": {
          "url": {
            "type": "string"
          },
          "drawingPath": {
            "type": "string"
          },
          "cwd": {
            "type": "string"
          },
          "chromePath": {
            "type": "string"
          }
        },
        "required": [
          "url",
          "drawingPath",
          "cwd"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "drawing": {
            "type": "string"
          },
          "url": {
            "type": "string"
          },
          "viewport": {
            "type": "object",
            "properties": {
              "width": {
                "type": "number"
              },
              "height": {
                "type": "number"
              }
            },
            "required": [
              "width",
              "height"
            ],
            "additionalProperties": false
          },
          "rows": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "part": {
                  "type": "string"
                },
                "kind": {
                  "type": "string",
                  "enum": [
                    "id",
                    "text"
                  ]
                },
                "expected": {
                  "type": "string"
                },
                "actual": {
                  "type": "string"
                },
                "status": {
                  "type": "string",
                  "enum": [
                    "pass",
                    "missing",
                    "hidden",
                    "region",
                    "order"
                  ]
                }
              },
              "required": [
                "part",
                "kind",
                "expected",
                "actual",
                "status"
              ],
              "additionalProperties": false
            }
          },
          "passed": {
            "type": "boolean"
          }
        },
        "required": [
          "drawing",
          "url",
          "viewport",
          "rows",
          "passed"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-screen-url",
        "drawing-unreadable",
        "unsafe-reference-svg",
        "empty-reference-parts",
        "duplicate-screen-id"
      ],
      "resource_operations": [
        "files.stat",
        "files.read",
        "browser.render"
      ]
    },
    {
      "operation": "formatScreenComparison",
      "input_schema": {
        "type": "object",
        "properties": {
          "report": {
            "type": "object",
            "properties": {
              "drawing": {
                "type": "string"
              },
              "url": {
                "type": "string"
              },
              "viewport": {
                "oneOf": [
                  {
                    "type": "object",
                    "properties": {
                      "width": {
                        "type": "number"
                      },
                      "height": {
                        "type": "number"
                      }
                    },
                    "required": [
                      "width",
                      "height"
                    ],
                    "additionalProperties": false
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "rows": {
                "oneOf": [
                  {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "part": {
                          "type": "string"
                        },
                        "kind": {
                          "type": "string"
                        },
                        "expected": {
                          "type": "string"
                        },
                        "actual": {
                          "type": "string"
                        },
                        "status": {
                          "type": "string"
                        }
                      },
                      "required": [
                        "part",
                        "kind",
                        "expected",
                        "actual",
                        "status"
                      ],
                      "additionalProperties": false
                    }
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "passed": {
                "type": "boolean"
              }
            },
            "required": [
              "drawing",
              "url",
              "viewport",
              "rows",
              "passed"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "report"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "markdown": {
            "type": "string"
          }
        },
        "required": [
          "markdown"
        ],
        "additionalProperties": false
      },
      "errors": [
        "invalid-comparison-report"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "files",
      "kind": "blob",
      "access": "read",
      "operations": [
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exists": {
                "type": "boolean"
              },
              "is_symlink": {
                "type": "boolean"
              },
              "size": {
                "type": "integer",
                "minimum": 0
              }
            },
            "required": [
              "exists",
              "is_symlink",
              "size"
            ],
            "additionalProperties": false
          },
          "name": "stat"
        },
        {
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "path": {
                "type": "string"
              }
            },
            "required": [
              "path"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": {
                "type": "string"
              }
            },
            "required": [
              "content"
            ],
            "additionalProperties": false
          },
          "name": "read"
        }
      ]
    },
    {
      "name": "browser",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "url": {
                "type": "string"
              },
              "drawing": {
                "type": "string"
              },
              "chromePath": {
                "type": "string"
              }
            },
            "required": [
              "url",
              "drawing",
              "chromePath"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "viewport": {
                "type": "object",
                "properties": {
                  "width": {
                    "type": "number"
                  },
                  "height": {
                    "type": "number"
                  }
                },
                "required": [
                  "width",
                  "height"
                ],
                "additionalProperties": false
              },
              "reference": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "kind": {
                      "type": "string",
                      "enum": [
                        "id",
                        "text"
                      ]
                    },
                    "value": {
                      "type": "string"
                    },
                    "visible": {
                      "type": "boolean"
                    },
                    "ownerId": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "bounds": {
                      "type": "object",
                      "properties": {
                        "x": {
                          "type": "number"
                        },
                        "y": {
                          "type": "number"
                        },
                        "width": {
                          "type": "number"
                        },
                        "height": {
                          "type": "number"
                        }
                      },
                      "required": [
                        "x",
                        "y",
                        "width",
                        "height"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "kind",
                    "value",
                    "visible",
                    "ownerId",
                    "bounds"
                  ],
                  "additionalProperties": false
                }
              },
              "actual": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "kind": {
                      "type": "string",
                      "enum": [
                        "id",
                        "text"
                      ]
                    },
                    "value": {
                      "type": "string"
                    },
                    "visible": {
                      "type": "boolean"
                    },
                    "ownerId": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "bounds": {
                      "type": "object",
                      "properties": {
                        "x": {
                          "type": "number"
                        },
                        "y": {
                          "type": "number"
                        },
                        "width": {
                          "type": "number"
                        },
                        "height": {
                          "type": "number"
                        }
                      },
                      "required": [
                        "x",
                        "y",
                        "width",
                        "height"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "kind",
                    "value",
                    "visible",
                    "ownerId",
                    "bounds"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "viewport",
              "reference",
              "actual"
            ],
            "additionalProperties": false
          },
          "name": "render"
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 20,
    "max_model_calls": 10
  },
  "conventions": []
}
```
</details>
