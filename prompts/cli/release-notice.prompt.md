# Release notice

Own `src/release-notice.mjs`. Tell people when a newer stable pdd release is available. Export async `releaseNotice({version, ci}, ports={})`, returning `{notice}`. With truthy `ci`, return an empty notice without a lookup. Otherwise call the injected `ports.latest()` once; the native default reads GitHub's public latest release for promptdriven/pdd with a one-second timeout and maps the response `tag_name` to `{tag}`. Bound the complete request and body read, and treat failures, non-success responses, malformed responses and timeouts as no notice. Never install software or write state.

Accept only stable versions of the form `MAJOR.MINOR.PATCH`, optionally prefixed with `v` or `alpha-v`, in both the installed version and the release's `tag_name`. Compare numeric components without loss of precision. A strictly newer release produces exactly `pdd <installed>: update available (<latest>). Run: npm install -g github:promptdriven/pdd\n`, with versions shown without a prefix. All other outcomes return an empty notice. Ignore remote text other than the validated tag.

## Dependencies

The native lookup uses Node's fetch and abort timer behind the injected port. The caller owns displaying the returned notice.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"6ab5ab14d2b984534a363ed47fb0e2376d58221c4781ceee8d50164e347f5667","entries":[{"operation":"releaseNotice","input_schema":{"type":"object","properties":{"version":{"type":"string"},"ci":{"type":"boolean"}},"required":["version","ci"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"notice":{"type":"string"}},"required":["notice"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[{"name":"release","kind":"port","access":"read","operations":[{"name":"latest","access":"read","arguments_schema":{"type":"object","properties":{},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"tag":{"type":"string"}},"required":["tag"],"additionalProperties":false}}]}],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
