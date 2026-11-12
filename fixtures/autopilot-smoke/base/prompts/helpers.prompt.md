# Smoke package helpers

Own `src/helpers.mjs`. Export three pure functions for finite number inputs.
`clamp(value, min = 0, max = 100)` returns the value bounded inclusively by min
and max, with min <= max; zero is a valid upper bound. `slugify(text)` trims a
string, lowercases it, replaces runs of non-ASCII-alphanumerics with `-`, and
removes leading/trailing hyphens. `sum(values)` adds a finite numeric array,
returning zero for an empty array. No external effects or dependencies.

The vendored base deliberately violates the clamp contract when max is zero.
Its ordinary native tests pass; the smoke bug issue supplies the missing failing
case. Preserve this seed defect until that sandbox issue is implemented.

## Dependencies

None; ECMAScript arithmetic and string operations suffice.

<details><summary>Runtime interface</summary>

```json
{"kind":"partial","status":"draft","prose_sha256":"","entries":[{"operation":"clamp","input_schema":{"type":"object","properties":{"value":{"type":"number"},"min":{"type":"number"},"max":{"type":"number"}},"required":["value","min","max"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"value":{"type":"number"}},"required":["value"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":2,"max_model_calls":0},"conventions":["Partial clamp contract only; native tests cover the other helpers."]}
```

</details>
