# Metrics capture

`src/metrics-capture.mjs` adapts observed workflow transitions to compact metrics facts. It does not select work, judge evidence, or advance workflows. Module functions `captureObservation` and `backfillRun` return facts; `recordObservation` sends facts through an injected store port. Callers provide event identity, UTC observation time and source identity. Preserve separate observations, including retries and contradictory facts. Backfill is a fallback for saved facts missing from the native journal, as selected by the command; it does not alter source identity or existing observations.

A workflow-created or launch-attempt observation is not a confirmed start. A confirmed start requires an explicit observation and carries its known origin (`autopilot`, `manual`, or `unknown`), launch linkage and installed/candidate versions when supplied. Readiness for independent validation is an explicit milestone with candidate identity, not internal review completion. Validation evidence is distinct from internal steps. Preserve observed outcome (`prompt-only` or `code`) without inferring it from a workflow name. A transition records the supplied step and status before subsequent transitions can overwrite it.

Backfill only fields present in the saved run, using their own timestamps. A saved run's creation time is not proof that its worker started. Missing start, origin, readiness, validation, outcome and intervention coverage remain unknown. Record only approved structured assistance categories and coverage limits; never copy summaries, questions, prompts, chats, approval text, credentials or arbitrary fields. Unknown fields are discarded. Reject invalid identities, times, event types and enumerations. Store failures are returned to the caller without disrupting workflow execution.

## Dependencies

The metrics event and store contract in [metrics model](metrics-model.prompt.md) governs the accepted event envelope and store port. Callers supply the actual workflow records and explicit observations; this module does no I/O except the injected recording port.

The observation envelope uses `schema`, `id`, `repo`, `issue`, `type`, `at`, `observedAt`, `source`, optional `attempt`, and a type-specific `data` object. Backfilled step completions use the saved `done` entry's timestamp and actual done or skipped status, without its summary. The caller supplies a stable prefix for each backfill identity. Reject any observation whose required envelope or type-specific values are invalid; omit invalid optional values rather than publishing arbitrary text. `recordObservation` calls `appendEvents({root, events})` on its injected store and returns `{ok, count}` or `{ok:false, error}`.

Backfill a saved skipped completion as skipped, never as a completed step.
