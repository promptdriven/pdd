# bytes

This module formats downloaded file sizes so they are easy to scan in a list. It owns byte-count formatting.

Public binding: module function `formatBytes(bytes)` in `src/bytes.js`, exported at `tiny-format/bytes`. It returns a string. The Runtime interface uses JSON transport: operation `formatBytes` takes an object with required `bytes` and no other properties, and returns an object with required string `text` and no other properties. `text` is the returned string. Its input schema admits representative JSON shapes for rejection; the native function rejects every non-number, including arbitrary JavaScript objects.

## Byte format

Accept only a nonnegative safe integer Number, including negative zero. Use powers of 1,024 for B, KiB, MiB, GiB, TiB and PiB, respectively. Select the largest unit whose size is no greater than the input, capped at PiB; zero uses B. Divide by that unit's size and round down to a whole number. Return its ungrouped decimal digits, one space, and the unit name. For example, 0 and -0 produce `0 B`, 1023 produces `1023 B`, 1024 and 1536 produce `1 KiB`, 1048576 produces `1 MiB`, and 1073741824 produces `1 GiB`.

## Refused counts

Negative values, fractions, non-number values, NaN, infinities and unsafe integers throw `RangeError` with `code` equal to `invalid-bytes`. Do not coerce inputs.

This is pure behavior: no external resources, operating-system commands or saved data. Preserve existing helpers and add no dependencies.

## Dependencies

None.

<details><summary>Runtime interface</summary>

```json
{"entries":[{"operation":"formatBytes","input_schema":{"type":"object","properties":{"bytes":{"oneOf":[{"type":"number"},{"type":"string"},{"type":"boolean"},{"type":"null"},{"type":"array","items":{"type":"number"}},{"type":"object","properties":{},"required":[],"additionalProperties":false}]}},"required":["bytes"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"text":{"type":"string"}},"required":["text"],"additionalProperties":false},"errors":["invalid-bytes"]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[],"status":"approved","prose_sha256":"e83587eee99b94a695caee65178e27a4e27f9316a2decdcb409c6fcfe4981b34"}
```
</details>