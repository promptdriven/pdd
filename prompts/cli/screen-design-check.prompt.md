# Screen design check

Own `src/screen-design-check.mjs`; export pure module functions
`lintScreenDesign({appMaps, stylesheets, prompts})` and
`evaluateScreenLook({viewport, reference, actual})`. These functions catch HTML
screens that drop their approved `.ui.svg` design by omitting stylesheets or CSS
classes before simulation, or by rendering bare browser defaults without painted
surfaces, matching colors, box bounds or card spacing during an optional look
comparison. Preserve supplied inputs without mutation, file reads, network calls
or AI calls.

## Stylesheet and class-name advisory (`lintScreenDesign`)

`lintScreenDesign({appMaps, stylesheets, prompts})` returns a fresh `{warnings}`
object whose `warnings` array holds sorted, deduplicated `Warning: SVG layout ...`
strings. Keep advisory behavior: warnings never refuse admission or approve a
prompt.

Inputs use the schemas in the Runtime interface below:

- `appMaps`: array of `{path, stylesheets, screens}` records from discovered
  `prompt-runtime.app-map.v1` maps. Each screen has `{id, prompt_path, source,
  format, stylesheets}`.
- `stylesheets`: array of `{path, content, error}` records for referenced CSS
  files (`content` is string when readable, else `null`; `error` is string when
  unreadable or unsafe, else `null`).
- `prompts`: array of `{path, prose, drawings}` records for inspected prompts,
  with Runtime interface blocks and comments already stripped from `prose` and
  linked `.ui.svg` repository-relative paths in `drawings`.

Inspect only screens where `source === "operation"` and `format === "html"`,
`prompts` contains an entry with `path === screen.prompt_path`, and that prompt's
`drawings` array is nonempty. SVG mockup screens (`source === "mockup"`) carry
their own SVG paint, and HTML screens without `.ui.svg` links declare no drawn
reference; emit no stylesheet warning for either.

For each eligible HTML screen, let `firstDrawing` be the lexicographically
smallest path in `prompt.drawings`, and let `effectiveStylesheets` be
`[...appMap.stylesheets, ...screen.stylesheets]` deduplicated in first-seen
order:

1. **No stylesheet in app map.** When `effectiveStylesheets` is empty, emit:
   `Warning: SVG layout <appMap.path> -> <prompt.path>: stylesheets: HTML screen "<screen.id>" links <firstDrawing> with no stylesheet in "stylesheets".`
2. **Missing or unreadable stylesheet.** When `effectiveStylesheets` is nonempty,
   look up each `cssPath` in `stylesheets` by `path === cssPath`. For any entry
   that is absent, has `error !== null`, or has `content === null`, emit:
   `Warning: SVG layout <appMap.path> -> <cssPath>: stylesheet: <error || "stylesheet is missing or unreadable">.`
3. **No design class named in prompt.** When `effectiveStylesheets` is nonempty
   and every referenced stylesheet has `error === null` and string `content`,
   extract CSS class selectors from each stylesheet: remove `/* ... */` block
   comments and single- or double-quoted CSS string literals, then inspect only
   selector text outside `{ ... }` declaration blocks and collect every
   `.([A-Za-z_-][A-Za-z0-9_-]*)` class name. When at least one effective
   stylesheet defines one or more class names, check whether `prompt.prose`
   either declares inline styles (`/\bstyle\s*=|<\s*style\b/i`) or mentions at
   least one extracted class name `name` on token boundaries
   (`(?<![A-Za-z0-9_-])\.?<name>(?![A-Za-z0-9_-])`, case-sensitive). If neither
   holds, choose the first effective stylesheet with at least one class selector
   (`firstSheet`) and its lexicographically smallest class name (`firstClass`),
   and emit:
   `Warning: SVG layout <prompt.path> -> <firstSheet.path>: stylesheet classes: HTML screen "<screen.id>" links <firstDrawing> and names no CSS class from its stylesheet (for example .<firstClass>).`
   A stylesheet that styles semantic elements or ids only and defines zero CSS
   classes emits no class-name warning.

Return `{warnings}` deduplicated and sorted in standard ascending code-unit
order.

## Optional look comparison (`evaluateScreenLook`)

`evaluateScreenLook({viewport, reference, actual})` compares rendered canvas and
box appearance within layout tolerances, never requiring pixel equality, and
returns a fresh `{rows, passed}` object. Each row is `{part, kind: "look",
expected, actual, status}` with `status` equal to `"pass"` or `"look"`, and
`passed` equal to `rows.every(row => row.status === "pass")`.

Format any `[r, g, b]` color (`0..255` integers) as lowercase `#rrggbb`, and
measure color distance with Euclidean RGB distance
`Math.hypot(r1 - r2, g1 - g2, b1 - b2)`:

1. **Canvas color row.** When `reference.canvasColor !== null`, emit first row
   `part: "canvas"`, `kind: "look"`, `expected: "canvas #<refHex>"`. If
   `actual.canvasColor !== null` and RGB distance is `<= 80`, set
   `status: "pass"` and `actual: "canvas #<actualHex>"`; otherwise set
   `status: "look"` and
   `actual: actual.canvasColor ? "canvas #<actualHex>" : "absent"`. When
   `reference.canvasColor === null`, emit no canvas row.
2. **Adjacent sibling spacing target.** For each `reference.boxes[i]` (`ref`),
   find earlier boxes `prev` in `reference.boxes.slice(0, i)`:
   - Vertical candidates have horizontal overlap
     `Math.min(ref.box.x + ref.box.width, prev.box.x + prev.box.width) - Math.max(ref.box.x, prev.box.x) > 0`
     and vertical gap `gap = ref.box.y - (prev.box.y + prev.box.height) >= 6`.
     If any exist, choose the candidate with the smallest `gap` (ties keep the
     earlier candidate) with `axis: "y"`.
   - Otherwise, horizontal candidates have vertical overlap
     `Math.min(ref.box.y + ref.box.height, prev.box.y + prev.box.height) - Math.max(ref.box.y, prev.box.y) > 0`
     and horizontal gap `gap = ref.box.x - (prev.box.x + prev.box.width) >= 6`.
     If any exist, choose the candidate with the smallest `gap` (ties keep the
     earlier candidate) with `axis: "x"`.
   - Otherwise the box has no spacing target (`spacing = null`).
3. **Painted box rows.** For each `ref` in `reference.boxes`, in order, emit a
   row with `part: "#<ref.id> look"`, `kind: "look"`, and `expected` equal to
   `"painted <round(ref.box.width)>×<round(ref.box.height)>"` followed by
   `" #<hex(ref.fill)>"` when `ref.fill !== null` and
   `", gap <round(spacing.gap)>px"` when `spacing !== null`.
   Match `hits = actual.boxes.filter(box => box.id === ref.id)`:
   - `hits.length === 0` -> `status: "look"`, `actual: "absent"`.
   - `hits.length > 1` -> `status: "look"`, `actual: "duplicate id"`.
   - `!hits[0].visible` -> `status: "look"`, `actual: "hidden/outside"`.
   - Otherwise let `hit = hits[0]` and collect failures in this order:
     a. **Box paint:** if `!hit.painted`, record `"unpainted box"`.
     b. **Box fill color:** when `ref.fill !== null` and
        (`reference.canvasColor === null` or
        `rgbDistance(ref.fill, reference.canvasColor) > 12`):
        if `hit.fill !== null` and `rgbDistance(ref.fill, hit.fill) > 90`,
        record `"color #<hex(hit.fill)>"`; else if `hit.fill === null`,
        `ref.stroke === null`, and (`reference.canvasColor === null` or
        `rgbDistance(ref.fill, reference.canvasColor) > 40`), record
        `"missing fill"`.
     c. **Box dimensions:** require `hit.box.width` within
        `[Math.max(12, ref.box.width * 0.5 - 12), ref.box.width * 1.8 + 24]`
        and `hit.box.height` within
        `[Math.max(12, ref.box.height * 0.5 - 12), ref.box.height * 1.8 + 24]`;
        outside either interval, record
        `"size <round(hit.box.width)>×<round(hit.box.height)>"`.
     d. **Box spacing:** when `spacing !== null` and `actual.boxes` has a single
        visible match `prevHit` for `spacing.prevId`, compute `actualGap` as
        `hit.box.y - (prevHit.box.y + prevHit.box.height)` for `axis === "y"` or
        `hit.box.x - (prevHit.box.x + prevHit.box.width)` for `axis === "x"`.
        Require `actualGap >= Math.min(2, spacing.gap * 0.25)` and
        `actualGap <= Math.max(spacing.gap * 3 + 24, 48)`; outside that range,
        record `"gap <round(actualGap)>px"`.
   - With no failures, set `status: "pass"` and `actual` to
     `"painted <round(hit.box.width)>×<round(hit.box.height)>"` followed by
     `" #<hex(hit.fill)>"` when `hit.fill !== null` and
     `", gap <round(actualGap)>px"` when `actualGap` was measured. With one or
     more failures, set `status: "look"` and `actual: failures.join("; ")`.

## Dependencies

None. Both operations are pure deterministic functions over supplied data.

<details><summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "1dff6d229de635d1197e07649a9703a6aa1a0aa88bb9cdfe2d77ad9851fd18df",
  "entries": [
    {
      "operation": "lintScreenDesign",
      "input_schema": {
        "type": "object",
        "properties": {
          "appMaps": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": { "type": "string" },
                "stylesheets": {
                  "type": "array",
                  "items": { "type": "string" }
                },
                "screens": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "id": { "type": "string" },
                      "prompt_path": { "type": "string" },
                      "source": { "type": "string" },
                      "format": { "type": "string" },
                      "stylesheets": {
                        "type": "array",
                        "items": { "type": "string" }
                      }
                    },
                    "required": ["id", "prompt_path", "source", "format", "stylesheets"],
                    "additionalProperties": false
                  }
                }
              },
              "required": ["path", "stylesheets", "screens"],
              "additionalProperties": false
            }
          },
          "stylesheets": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": { "type": "string" },
                "content": {
                  "oneOf": [{ "type": "string" }, { "type": "null" }]
                },
                "error": {
                  "oneOf": [{ "type": "string" }, { "type": "null" }]
                }
              },
              "required": ["path", "content", "error"],
              "additionalProperties": false
            }
          },
          "prompts": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "path": { "type": "string" },
                "prose": { "type": "string" },
                "drawings": {
                  "type": "array",
                  "items": { "type": "string" }
                }
              },
              "required": ["path", "prose", "drawings"],
              "additionalProperties": false
            }
          }
        },
        "required": ["appMaps", "stylesheets", "prompts"],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "warnings": {
            "type": "array",
            "items": { "type": "string" }
          }
        },
        "required": ["warnings"],
        "additionalProperties": false
      },
      "errors": []
    },
    {
      "operation": "evaluateScreenLook",
      "input_schema": {
        "type": "object",
        "properties": {
          "viewport": {
            "type": "object",
            "properties": {
              "width": { "type": "number", "exclusiveMinimum": 0 },
              "height": { "type": "number", "exclusiveMinimum": 0 }
            },
            "required": ["width", "height"],
            "additionalProperties": false
          },
          "reference": {
            "type": "object",
            "properties": {
              "canvasColor": {
                "oneOf": [
                  {
                    "type": "array",
                    "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                    "minItems": 3,
                    "maxItems": 3
                  },
                  { "type": "null" }
                ]
              },
              "boxes": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": { "type": "string" },
                    "box": {
                      "type": "object",
                      "properties": {
                        "x": { "type": "number" },
                        "y": { "type": "number" },
                        "width": { "type": "number", "exclusiveMinimum": 0 },
                        "height": { "type": "number", "exclusiveMinimum": 0 }
                      },
                      "required": ["x", "y", "width", "height"],
                      "additionalProperties": false
                    },
                    "fill": {
                      "oneOf": [
                        {
                          "type": "array",
                          "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                          "minItems": 3,
                          "maxItems": 3
                        },
                        { "type": "null" }
                      ]
                    },
                    "stroke": {
                      "oneOf": [
                        {
                          "type": "array",
                          "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                          "minItems": 3,
                          "maxItems": 3
                        },
                        { "type": "null" }
                      ]
                    }
                  },
                  "required": ["id", "box", "fill", "stroke"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["canvasColor", "boxes"],
            "additionalProperties": false
          },
          "actual": {
            "type": "object",
            "properties": {
              "canvasColor": {
                "oneOf": [
                  {
                    "type": "array",
                    "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                    "minItems": 3,
                    "maxItems": 3
                  },
                  { "type": "null" }
                ]
              },
              "boxes": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "id": { "type": "string" },
                    "visible": { "type": "boolean" },
                    "painted": { "type": "boolean" },
                    "box": {
                      "type": "object",
                      "properties": {
                        "x": { "type": "number" },
                        "y": { "type": "number" },
                        "width": { "type": "number", "minimum": 0 },
                        "height": { "type": "number", "minimum": 0 }
                      },
                      "required": ["x", "y", "width", "height"],
                      "additionalProperties": false
                    },
                    "fill": {
                      "oneOf": [
                        {
                          "type": "array",
                          "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                          "minItems": 3,
                          "maxItems": 3
                        },
                        { "type": "null" }
                      ]
                    },
                    "stroke": {
                      "oneOf": [
                        {
                          "type": "array",
                          "items": { "type": "integer", "minimum": 0, "maximum": 255 },
                          "minItems": 3,
                          "maxItems": 3
                        },
                        { "type": "null" }
                      ]
                    }
                  },
                  "required": ["id", "visible", "painted", "box", "fill", "stroke"],
                  "additionalProperties": false
                }
              }
            },
            "required": ["canvasColor", "boxes"],
            "additionalProperties": false
          }
        },
        "required": ["viewport", "reference", "actual"],
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
                "part": { "type": "string" },
                "kind": { "type": "string", "enum": ["look"] },
                "expected": { "type": "string" },
                "actual": { "type": "string" },
                "status": { "type": "string", "enum": ["pass", "look"] }
              },
              "required": ["part", "kind", "expected", "actual", "status"],
              "additionalProperties": false
            }
          },
          "passed": { "type": "boolean" }
        },
        "required": ["rows", "passed"],
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
