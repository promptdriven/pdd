# Setup terminal policy

Own `src/setup-interaction.mjs`. Export module function
`setupMayAsk({yes = false, stdinIsTTY = false, stdoutIsTTY = false} = {})`
returning a Boolean. Setup may ask questions only when yes is false and both
streams are terminals. This shared hook keeps optional setup actions from
blocking agents or interpreting `--yes` as consent to extra writes.

The caller supplies actual stream TTY flags and the parsed `--yes` flag. Missing
flags default false. Return false whenever yes is truthy; otherwise return the
Boolean conjunction of the two TTY flags. The function has no effects.

## Dependencies

None; this policy uses only Boolean operations.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","entries":[{"operation":"setupMayAsk","input_schema":{"type":"object","properties":{"yes":{"type":"boolean"},"stdinIsTTY":{"type":"boolean"},"stdoutIsTTY":{"type":"boolean"}},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"mayAsk":{"type":"boolean"}},"required":["mayAsk"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":["Wrap the native Boolean result as mayAsk."]}
```

</details>
