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
spending a call. For port 80, bare 127.0.0.1 and localhost Hosts and their http Origins are the same origin as the explicit :80 forms; other ports require their actual port. Do not enable CORS. This prevents a remote page or DNS rebinding from spending the owner's
budget through localhost. Named API requests with a nonempty browser Sec-Fetch-Dest are refused403 before
dispatch: images, stylesheets, scripts and navigations must never spend AI calls from model markup. Curl and
fetch/XHR have absent or empty destinations and continue normally. Require origin-form request targets, bound bodies to 1 MiB UTF-8 and concurrent
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

When the model has an app map, serve its real Screen at GET/HEAD / using the owner-authenticated Screen
transport /v1/try/<id>/screen/. Forward only the allowlisted shell, renderer, stylesheet, state, action lookup,
app/open and act resources beneath local /__pdd/screen/. Never forward a browser Authorization, Cookie, upstream
URL, engine token or arbitrary resource path. The remote trusted shell and shared hosted renderer own drawing
and events. The browser communicates only with localhost; pdd adds its own owner credentials upstream.
GET / only reads the Screen shell; the explicit Open the app action spends the existing runtime budget.
App-map Stories may have zero HTTP entries. For that case open the same listener and explicitly say
"Screen only (no named HTTP routes)." Do not ask the person to add an HTTP route to use the Screen.
Only authenticated pinned metadata grants Screen capability; a locally detected map is not remote admission.
If neither capability exists and a local app map was selected, explain that this saved Try has no Screen map
and give the exact pdd try STORY --serve PORT --new recovery (including --app-map with the selected map path relative to the invocation directory, safely shell-quoted).
Do not silently stop, replace or reset the saved session. If neither capability exists and no map was selected,
say the Story has neither a Screen app map nor named HTTP routes; explain both valid ways to provide one.
Reserve GET/HEAD / and every /__pdd/screen/ path when a Screen
exists; conflicting named routes refuse startup. Without an app map, keep ordinary named-route behavior.
Screen requests share all local origin, body, pending-limit and cancellation guards. Forward UTF-8 trusted
assets and JSON with bounded responses (16 MiB), no redirects, no cookies or CORS headers, no caching, nosniff,
no-referrer and a CSP allowing only same-origin trusted scripts/styles/connects, data-only images (no same-origin image requests) and script-free
sandboxed frames. JSON action bodies go through the existing remote action ledger; never retry POST after a
lost answer. A lost POST returns uncertainty to the driver, which reads its persisted action ID. Stop prevents
new upstream work and interrupts outstanding reads. Print the actual Screen URL as well as named API routes.

## Dependencies

- [Runtime client](runtime-client.prompt.md): required generation/runtime context for owner-authenticated metadata,
  exactly-once calls and session lifecycle.
- [Preflight](runtime-preflight.prompt.md): required generation/runtime input-schema checking.
- Engine prompt_runtime/program_door_routes.prompt.md: required route-title contract, supplied as the same method
  and path fields in the owner model; no raw engine import or private credentials are needed in this client.

## Usage for named HTTP routes
Use authenticated owner model calls.cap/remaining at startup and print the short session usage line on stderr. For each named API response, attach the runtime-output Try usage headers without changing program status, headers outside the reserved usage names, or body. Confirmed calls use normalized call receipt usage/remaining and the known session cap. Wrapper errors retain known receipt usage or unknown when unconfirmed. Local pre-dispatch errors use zero calls and the last known remaining, labeled x-pdd-usage-source:last-known; confirmed receipt headers use runtime. Reserved x-pdd-* usage headers override any program-supplied lookalike. Never make a model call or repeat dispatch for accounting. Screen proxy behavior stays with its existing contract.

Usage normalization/formatting/header names are owned by [runtime output](runtime-output.prompt.md#try-usage), required generation/runtime context.

## Progress in the pdd window
Each API call can take many seconds, so the pdd window logs each request on stderr, like a local server: `<METHOD> <path>: running on the Try…` before the call, then `<METHOD> <path>: <status> in N s`, or the error status and its plain reason. Screen requests log only their failures. A busy port stops startup with `pdd try: port N is in use by another program. Stop it, or run pdd try <story> --serve <N+1>.` (exit 125).
