# Detailed interpreter version

Own `src/interpreter-version.mjs`. Export asynchronous module function
`runDetailedVersion({version, env={}}, ports={})`, returning exactly
`{exit_code, stdout, stderr}`. Native env is the full invocation environment;
the Runtime env schema is its closed fixture projection, not a native filter.
This diagnostic must keep local version reporting available when the
interpreter cannot be read. `version` is the CLI's already
validated package version. Behavioral refinement permits this new module and
injected callbacks; it changes no existing module signature or version output.

## Read one metadata answer

All outside work uses injected callbacks. Call
`ports.resolveOrigin({env: addressEnv})` once. addressEnv contains only
PDD_RUNTIME_URL when present. Its default adapts the existing `runtimeOrigin(env)` export from the address owner
below to `{valid,origin}`, catching rejection as `{valid:false,origin:""}`.
Use that result; do not create another address setting or default.
If invalid, finish unknown before reading a token. Otherwise call
`ports.readToken({timeoutMs:2000})` once. Its native default runs only
`gh auth token`, ignores stdin and captures both output streams. Use the full
native invocation environment. Return trimmed successful stdout as `{token}`, otherwise `{token:""}`. No login, account
lookup or auth-status command runs. A missing, empty or failed token read finishes
unknown without network access. Tokens stay only in memory and request headers.

With a token call `ports.getMetadata({origin,path:"/v1/version",method:"GET",
token,timeoutMs:10000,redirect:"manual"})` once. Its native default sends an
Authorization Bearer header through the injected fetch transport, with TLS and
origin policy from the address owner, bounds the request and response-body read
to ten seconds, and returns `{status,body}` with body as UTF-8 response text.
Abort timeout work; never follow redirects, retry, upload source, write state,
start lint/check/Try jobs, query a model or make an AI call. Any callback throw,
network error, timeout, non-200 status, invalid JSON, non-object JSON or missing
or malformed `engine_sha` finishes unknown. A valid engine_sha is exactly 40
hexadecimal digits, printed in lowercase; never use the CLI's source revision
or a model name as interpreter identity. Never print raw server prose or errors.

## Result

Every outcome returns exit_code 0 and stderr "". Every written line ends with
one newline. Begin stdout with `PDD CLI: VERSION`, substituting version unchanged.
Unknown adds only `PDD interpreter: unknown`. A valid metadata answer adds
`PDD interpreter: SHA`, then `Interface formats: VALUE`, `Test formats: VALUE`
and `App-map formats: VALUE`, in that order. VALUE uses `formats.interface`,
`formats.test` and `formats.app_map` respectively. A list of at most 32 strings,
each matching `^prompt-runtime\.[a-z0-9][a-z0-9._-]{0,127}$`, prints its exact IDs
in received order joined by `, `; an empty list prints `none`. Missing or malformed
lists print `unknown` for that line. Ignore all other metadata, including model,
api_version and arbitrary server messages. This prevents control characters and
unrelated remote prose from reaching terminal output.

## Dependencies

- [Runtime address owner](runtime-client.prompt.md#setup): required native
  generation/verification context for the existing `runtimeOrigin(env)` export.
  Runtime execution receives its resolved value through `origin.resolve`;
  this resource adapter catches rejection but does not own address policy.
- Native defaults use Node child-process and abortable fetch facilities behind
  the injected callbacks above. Runtime resources bind those same callbacks;
  no host process or live service is used in a scenario.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"28c27f49f3ead102ed8ae1d740d3f43661e4dd7d297778e0e99e6f1fee65cfb7","entries":[{"operation":"runDetailedVersion","input_schema":{"type":"object","properties":{"version":{"type":"string"},"env":{"type":"object","properties":{"HOME":{"type":"string"},"PATH":{"type":"string"},"CODEX_HOME":{"type":"string"},"CLAUDE_CONFIG_DIR":{"type":"string"},"PDD_RUNTIME_URL":{"type":"string"}},"required":[],"additionalProperties":false}},"required":["version"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exit_code":{"type":"integer"},"stdout":{"type":"string"},"stderr":{"type":"string"}},"required":["exit_code","stdout","stderr"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[{"name":"origin","kind":"port","access":"read","operations":[{"name":"resolve","access":"read","arguments_schema":{"type":"object","properties":{"env":{"type":"object","properties":{"PDD_RUNTIME_URL":{"type":"string"}},"required":[],"additionalProperties":false}},"required":["env"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"valid":{"type":"boolean"},"origin":{"type":"string"}},"required":["valid","origin"],"additionalProperties":false}}]},{"name":"credentials","kind":"port","access":"read","operations":[{"name":"readToken","access":"read","arguments_schema":{"type":"object","properties":{"timeoutMs":{"type":"integer"}},"required":["timeoutMs"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"token":{"type":"string"}},"required":["token"],"additionalProperties":false}}]},{"name":"metadata","kind":"port","access":"read","operations":[{"name":"get","access":"read","arguments_schema":{"type":"object","properties":{"origin":{"type":"string"},"path":{"type":"string"},"method":{"type":"string"},"token":{"type":"string"},"timeoutMs":{"type":"integer"},"redirect":{"type":"string"}},"required":["origin","path","method","token","timeoutMs","redirect"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"status":{"type":"integer"},"body":{"type":"string"}},"required":["status","body"],"additionalProperties":false}}]}],"limits":{"max_steps":12,"max_model_calls":6},"conventions":[]}
```
</details>
