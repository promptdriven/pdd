# Checkup Interactive Repair Sessions

`pdd.checkup_interactive_session` defines the engine-agnostic session contract
used by interactive prompt repair. It does not present a CLI by itself, apply
patches, or write files. TTY, Pi, or other backends should implement the same
`InteractiveRepairSession` protocol and pass the shared contract tests.

## Hybrid backend context (#1434)

Block 0 ([#1434](https://github.com/promptdriven/pdd/issues/1434)) records a
**Hybrid** decision: Pi may generate contextual QA and repair proposals when
available, but **Python always owns** numbered menus, choice validation,
`--apply` gating, session persistence, and file mutation. See
`docs/checkup_interactive_session_spike.md` for the ownership boundary.

This module is the shared contract (#1435). Future `TtyInteractiveSession` and
Pi proposal adapters (#1436+) call `present_finding`, `record_choice`, and
`approved_patches()` from Python orchestration code — they do not delegate menus
to Pi.

## API contract

The module exposes these value and protocol types:

- `ApprovedPatch`: a typed patch approval with `kind`, `target`, `anchor`,
  `replacement`, and optional `finding_id` (stamped from `record_choice` when
  absent).
- `RepairOption`: a presented repair option with a user-visible `label`,
  `preview`, and associated non-optional `ApprovedPatch`.
- `InteractiveRepairSession`: a structural protocol with `seed(report)`,
  `present_finding(finding_id)`, `ask(question)`, `record_choice(finding_id,
  option)`, and `approved_patches()`.
- `FakeInteractiveSession`: the deterministic in-memory backend used by tests.

`approved_patches()` must return only `ApprovedPatch` instances that came from
recorded approving choices. Raw model text, free-form answers, skipped findings,
and custom no-patch choices must not appear in the returned list. Non-approving
choices still carry typed `ApprovedPatch` objects, using kinds such as `skip` or
`custom_no_patch`.

## Fake backend

`FakeInteractiveSession` is the deterministic test backend. Tests may seed it
with findings, scripted options, scripted answers, and expected choices. It keeps
all state in memory and should be usable in the same contract-test matrix as
future TTY or Pi backends.

## Side-effect boundary

The session layer is read-only with respect to the filesystem:

- it may keep in-memory session state,
- it may return typed approved patches,
- it must not write session artifacts,
- it must not apply patches,
- it must not normalize or enforce repository-boundary path policy for patch
  targets.

Persistence and patch application belong to later orchestration and apply
layers.

## Session artifacts

When a backend or orchestration layer persists an interactive session, use one
of these paths:

```text
.pdd/evidence/checkups/sessions/<run_id>.jsonl
.pdd/evidence/checkups/sessions/<run_id>.json
```

Use `.jsonl` for event-stream style sessions, such as Pi. Use `.json` for a
full snapshot style session, such as a TTY wrapper.

### JSONL event records

Each line is one JSON object. Records should include stable `type`, `run_id`,
and timestamp fields, plus the fields for that event type.

Recommended event types:

- `session_started`: includes backend name and report summary.
- `finding_presented`: includes `finding_id` and the options shown.
- `question_answered`: includes the question and a summarized or redacted
  answer.
- `choice_recorded`: includes `finding_id`, selected option label, and typed
  patch metadata when a patch was approved.
- `session_completed`: includes counts for findings presented, choices
  recorded, questions answered, and approved patches.

Example:

```json
{"type":"finding_presented","run_id":"20260606T120000Z","finding_id":"R2-missing-vocabulary","options":[{"label":"A","preview":"--- prompt\n+++ prompt\n...","patch":{"kind":"vocab_definition","target":"prompts/refund_python.prompt","anchor":{"finding_id":"R2-missing-vocabulary","line":42},"replacement":"- Remaining refundable amount: captured amount minus successful refunds minus pending refunds."}}]}
```

### JSON snapshot records

A `.json` artifact should contain the same logical data as the event stream:

```json
{
  "schema_version": 1,
  "run_id": "20260606T120000Z",
  "backend": "tty",
  "report_summary": {},
  "findings": [],
  "options_shown": [],
  "choices": [],
  "qa_transcript_summary": [],
  "approved_patches": []
}
```

### Redaction

Artifacts may contain prompt snippets, diffs, paths, and human answers. Writers
must redact provider secrets, bearer tokens, API keys, authorization headers,
URL credentials, and other secret-like values before persisting artifacts.
