# Real localhost endpoints for a Try session

Own src/try-http.mjs. Export `openServe(context, test, sessionId, options)` for runTry's --serve mode.
Load the uploaded session's model through authenticated GET /v1/try/<id>/model. Refuse unavailable or ambiguous
route metadata before opening a port; never guess routes from operation names, tests, or local code. The engine's
route label is input_schema.title = `HTTP METHOD /path`, optionally with whole `:name` parameter segments.
Only declared entries returned by the model are callable. Identical method/path routes are ambiguous.

Listen on 127.0.0.1 only, at the --serve port (default 8080); report the URL and named routes. For each matched
request serialize dispatch on this session through runDoorCall, retaining the runtime's sign-in, budgets, saved
world and exactly-once transport. A stopped server sends no further calls. Ctrl-C closes the listener and does
not stop or reset the remote Try. Unknown route/method returns 404 without an AI call. HEAD may use GET while
suppressing the response body; a GET fallback receives GET in its method input. Paths decode UTF-8 parameters once; malformed escapes return 400.

Reject an unexpected Host, any non-same-origin Origin and Sec-Fetch-Site cross-site before reading a body or
spending a call. Do not enable CORS. This prevents a remote page or DNS rebinding from spending the owner's
budget through localhost. Require origin-form request targets, bound bodies to 1 MiB UTF-8 and concurrent
accepted requests to 32. Read bodies with a finite timeout. No shell or upstream URL comes from a request.

Input adaptation is generic and schema-directed. If an entry declares method, path, query, params, headers or
body, those fields receive the corresponding request component (only fields declared in the object schemas).
A query object receives declared query properties; a params object receives declared route parameters.
Other declared fields are direct route parameters, query values or fields of a JSON object body, in that order.
Query/path text converts to the declared primitive type: strings unchanged, true/false for booleans and JSON
numbers for finite numbers/integers. Arrays receive repeated query values. Reject duplicate scalar query fields,
unknown query names or an invalid input with 400 before a model call. JSON bodies receive parsed values;
string body fields receive exact UTF-8 text. Omit missing optional fields. Do not invent required values.

The result has integer status 200..599. If body is declared, return its string bytes or JSON serialization of
its value; otherwise serialize the result fields other than status and headers as a JSON object. Preserve
program response headers, including arrays of header values; validate names and values, remove hop-by-hop
headers and recompute content-length. Use application/json for JSON values unless the program supplies a
content-type. Responses to HEAD and statuses 204/304 have no body. Malformed program responses, stopped
sessions, exhausted budgets, lost outcomes and other wrapper failures return 502 with a plain `pdd try:` reason;
program-generated error statuses remain intact. Never return gh credentials, stacks or engine URLs.

If the model has an app map, the web Screen is a separate optional capability. Without a local Screen adapter,
print a clear short note explaining that the hosted Try Screen remains the way to click through it. Do not serve
a fake screen or silently turn GET / into a developer form. Named HTTP routes still work normally.

## Dependencies

- [Runtime client](runtime-client.prompt.md): required generation/runtime context for owner-authenticated metadata,
  exactly-once calls and session lifecycle.
- [Preflight](runtime-preflight.prompt.md): required generation/runtime input-schema checking.
- Engine prompt_runtime/program_door_routes.prompt.md: required route-title contract, supplied as the same method
  and path fields in the owner model; no raw engine import or private credentials are needed in this client.
