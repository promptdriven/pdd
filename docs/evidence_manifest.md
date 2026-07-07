# Evidence Manifests

Evidence manifests are optional JSON audit receipts for completed PDD runs. They
do not replace core dumps: core dumps diagnose exceptional failures, while an
evidence manifest records routine provenance for a successful command.

## Commands

Pass `--evidence` to supported command invocations:

```bash
pdd generate prompts/refund_python.prompt --output src/refund.py --evidence
pdd sync refund --evidence
pdd test --manual prompts/refund_python.prompt src/refund.py --evidence
pdd verify prompts/refund_python.prompt src/refund.py verify.py --evidence
pdd detect --stories --evidence
pdd change --manual change.prompt src/refund.py prompts/refund_python.prompt --evidence
```

Manifests are written under:

```text
.pdd/evidence/runs/<run_id>.json
.pdd/evidence/devunits/<basename>.latest.json
```

The versioned run path preserves audit history. The latest path provides a
stable lookup for downstream automation.

Interactive prompt-repair sessions are checkup evidence artifacts, but they are
not evidence manifests and are not written by the session protocol layer itself.
Backend or orchestration code may persist them under:

```text
.pdd/evidence/checkups/sessions/<run_id>.json
.pdd/evidence/checkups/sessions/<run_id>.jsonl
```

See `docs/checkup_interactive_session.md` for the session API contract and
artifact schema.

Snapshot-enabled runs also write replay artifacts:

```bash
pdd preprocess prompts/refund_python.prompt --snapshot
pdd generate prompts/refund_python.prompt --output src/refund.py --snapshot-context
pdd sync refund --snapshot-context
pdd replay .pdd/evidence/runs/<run_id>.json
```

The run manifest remains `.pdd/evidence/runs/<run_id>.json`. Replayable
expanded-prompt and dynamic-context artifacts live in the sibling directory
`.pdd/evidence/runs/<run_id>/`.

Snapshot manifests use **schema version 1**. Evidence manifests produced with
`--evidence` use **schema version 2** and may embed a `context_snapshot` block
pointing at the v1 snapshot manifest. Pass either file to `pdd replay`; replay
resolves linked snapshot metadata and verifies the expanded prompt hash.

Do not combine `pdd preprocess --recursive` with `--snapshot` when the prompt
uses `<shell>`, `<web>`, or `query=` includes; recursive mode defers those tags
so nothing is captured.

Enforce policy on latest manifests before merge:

```bash
pdd checkup gate
pdd checkup gate <devunit> --json
pdd checkup snapshot prompts/critical_python.prompt
```

## Contents

Schema version 2 records:

- command, timestamp, PDD version, model, temperature, and reported cost
- prompt and generated-output SHA-256 hashes when their paths are available
- deterministic local include hashes found directly in the prompt; for `mode="compressed"` includes, both `source_sha256` and `compressed_sha256` are recorded along with `estimated_tokens`
- contract coverage status when the prompt has contract rules
- available validation outcomes and references to existing logs
- `generation.grounding` provenance (added in schema v2; see "Grounding
  Provenance" below). Older manifests emitted with schema v1 omit this object.
- optional `generation.compression` and `generation.agentic_fallback` metadata
  for sync runs that used compressed context or agentic fallback.

`expanded_sha256` is the SHA-256 of the prompt after `pdd.preprocess` with
`recursive=True` and `double_curly_brackets=False` (the same deterministic
include expansion used before generation). `context.includes` uses the shared
include grammar (`path=` attributes, self-closing tags, backtick includes, and
`include-many`) and skips include-looking text inside fenced or inline code.
If a prompt uses shell, web, variable, query-based, or otherwise effectful
expansion, `expanded_sha256` is `null` rather than a guessed value.

When snapshotting is enabled, the run manifest records the expanded prompt hash, whether nondeterministic tags were present, and the artifact paths and SHA-256 hashes for captured shell output, web content, and semantic include-query output. Static prompts with only deterministic includes record that no nondeterministic context was captured. Shell/web snapshots are redacted before hashing and storage for known authorization headers, bearer/basic tokens, URL credentials, provider keys, and secret-like assignments; metadata records whether redaction changed content. Raw environment dumps and unredacted bearer/API tokens must not be persisted.

`pdd replay` reads a run artifact and reconstructs the expanded prompt context from the recorded snapshots. A successful replay means the prompt/context hash matches the original run; it does not assert that a later LLM generation will produce identical code.

Missing stories or contracts are reported as `not_applicable`; they do not make
an otherwise successful command fail. The schema is packaged at
`pdd/schemas/evidence_manifest.schema.json`.

### Grounding Provenance

Each manifest also records a `generation.grounding` object describing which
few-shot examples (if any) were injected by PDD Cloud grounding, plus any
`<pin>` / `<exclude>` overrides and whether a reviewer was involved:

```json
"generation": {
  "grounding": {
    "mode": "cloud",
    "selected_examples": [
      {
        "module": "refund_payment",
        "id": "ex-123",
        "title": "Refund payment example",
        "prompt_sha256": "…",
        "code_sha256": "…",
        "similarity": 0.91,
        "source": "cloud-history"
      }
    ],
    "pinned": ["refund_payment"],
    "excluded": ["legacy_refund_module"],
    "reviewed": true
  }
}
```

- `mode` is one of `cloud`, `local`, or `unavailable`. Local / no-cloud runs
  record `unavailable` rather than failing.
- `selected_examples[].prompt_sha256` / `code_sha256` / `similarity` / `source`
  are populated when the cloud reports them; missing fields are omitted rather
  than guessed.
- `reviewed` is `true` only when `--review-examples` was supplied, every
  `examplesUsed` entry has a matching pre-generation accept (via `<pin>` tags
  reviewed before the generate call), and cloud did not return additional
  examples that were not pre-approved.
- `selected_examples` preserves cloud `id` / `title` when present; `module` is
  always set (`module`, `slug`, or `id`).
- The legacy top-level `grounding_examples` array is preserved for backward
  compatibility and mirrors `generation.grounding.selected_examples` when
  present.

See `docs/grounding_policy.md` for the optional CI policy that consumes this
provenance (`.pdd/grounding_policy.yaml`, future grounding `pdd checkup gate`
integration). Contract waivers appear under `contracts.waivers` when prompts
include `<waivers>` blocks.

### Sync Compression and Agentic Fallback

Sync runs may also record additive metadata under `generation`:

```json
"generation": {
  "compression": {
    "enabled": true,
    "requested": true,
    "used": true,
    "mode": "compressed-sync-context",
    "phases": [
      {"phase": "generate", "used": true, "source_count": 4},
      {"phase": "verify", "used": true, "source_count": 5},
      {"phase": "fix", "used": false, "unavailable_reason": "prompt source missing"}
    ],
    "source_counts": {"tests": 3, "examples": 1},
    "source_hashes": [{"path": "tests/test_refund.py", "sha256": "..."}],
    "compressed_sha256": "...",
    "budget_tokens": 6000,
    "original_tokens_estimate": 18000,
    "compressed_tokens_estimate": 4200,
    "unavailable_reason": null
  },
  "agentic_fallback": {
    "attempted": true,
    "used": false,
    "phases": ["fix"],
    "reason": "local fix loop succeeded",
    "provider": "codex",
    "tool": "agentic-fix"
  }
}
```

`generation.compression` records whether compressed sync context was requested
and used, which phases received it, source counts/hashes, size estimates, and a
reason when compression was unavailable. `phases` may be a compact list of phase
names for callers that only have summary data, or a list of per-phase metadata
objects from sync's phase package builder. It must not include raw compressed
prompt, test, example, contract, or repair text.

`generation.agentic_fallback` records whether an agentic fallback was attempted
or used, which phases were involved, why fallback occurred, and provider/tool
metadata when available.

### Story Regression Coverage

The story regression lane (`make regression-stories`) emits a deterministic,
machine-readable coverage artifact alongside the run/devunit manifests. It
measures the **executable** `@pytest.mark.story` suite — distinct from the
LLM-backed `pdd detect --stories` validation — and is computed without any LLM
calls from the marker/traceability API and the story gate statuses.

Artifacts are written under:

```text
.pdd/evidence/stories/coverage.latest.json
.pdd/evidence/stories/runs/<run_id>.json
```

The `*.latest.json` path is the stable lookup for downstream automation
(repo-health dashboard in `pdd_cloud`, `pdd checkup`); the per-run snapshot
preserves history so trend can be computed downstream. This mirrors the
`runs/<run_id>.json` + `*.latest.json` convention used by evidence manifests.

The artifact uses an integer `schema_version` and is packaged at
`pdd/schemas/story_coverage.schema.json`. Fields:

- `schema_version` — integer schema version for the artifact (bumped on any
  breaking field change).
- `status` — `"ok"` only for a real measurement with pass/fail and freshness
  verdicts, or `"not_applicable"` when `story_count` is `0` or the upstream
  marker/traceability API or gate statuses are absent (the degraded case
  described below). Downstream consumers
  (`pdd_cloud`, `pdd checkup`) must branch on this field to distinguish a real
  measurement from a degraded one.
- `run_id` / `generated_at` — the per-run snapshot identifier and the ISO-8601
  UTC timestamp at which the artifact was emitted.
- `story_count` — total stories discovered.
- `story_backed_test_count` — collected `-m story` test items (parametrizations
  count individually, matching the "142 tests" example).
- `stories_covered` — distinct stories with at least one passing, non-stale
  regression test. Collection-only marker data is not enough to award coverage
  credit.
- `story_coverage_pct` — `stories_covered / story_count`, or `null` when
  `story_count` is `0` or pass/fail verdicts are unavailable (no
  division-by-zero; never reported as `0%` in degraded mode).
- `pass_rate` / `passing_test_count` — over collected story tests when real
  pass/fail verdicts are available. `pass_rate` is a fraction in `0.0..1.0`,
  not a percentage. When the emitter only has collection data, `pass_rate` is
  `null` and `passing_test_count` is `0`; it must not infer passing tests from
  collected markers. `skip`/`xfail` items are excluded from both the pass-rate
  and the "covered" count.
- `gap_stories[]` / `orphan_tests[]` — optional dashboard hints (stories with no
  test; story-marked tests pointing at no known story).

When the upstream marker/traceability API or gate statuses are unavailable (the
executable story suite is not yet present), the emitter writes a well-formed
artifact with `status: "not_applicable"` and unavailable pass-rate fields rather
than failing or overstating pass results — the same degradation convention used
elsewhere for missing stories/contracts.

## Verification

For this feature, use the focused pytest gate (not full `pytest -q` collection
on every environment):

```bash
pytest -q tests/commands/test_evidence.py tests/test_evidence_manifest.py tests/test_context_snapshot_replay.py tests/test_context_snapshot_policy.py
```

`pdd sync --evidence` records `unit_tests` / `verify` as `passed` or `failed`
only when those operations appear in `sync_main` results; otherwise the receipt
uses `not_available` or `not_applicable`.
