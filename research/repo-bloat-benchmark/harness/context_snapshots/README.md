# Context-snapshot instrumentation

Implements design.md **§6.2 tap 1** — the v2 primary instrument. Captures the
byte-exact composed context of every model request an agent CLI makes, then
turns the per-request series into the pre-registered metric families:
context-window **penetration** and the **iteration trajectory** (H2).

## Pieces

| Module | Role |
|--------|------|
| `proxy.py` | `RecordingProxy` — local HTTP relay; archives request/response bodies + provider `usage` per request; detects edit tool calls (first-edit boundary) |
| `schema.py` | `SnapshotRecord` (one per request) + JSONL read/write |
| `attribution.py` | `TreeIndex` — normalized-line index of the materialized variant; attributes surfaced content to core / distractor / ambiguous / unknown; `reconcile_with_usage` caps estimates at provider counts |
| `iteration_analyzer.py` | `analyze_run` — per-iteration token/composition series, early/middle/late phases, `growth_shape` (gradual/step/plateau/sawtooth), first-edit boundary |
| `session_parser.py` | tolerant parser for the CLI's own session/rollout JSONL + `reconcile` cross-check against the proxy record |

## Usage sketch

```python
from harness.context_snapshots import (
    RecordingProxy, TreeIndex, analyze_run, parse_session_log, reconcile,
)

proxy = RecordingProxy(
    upstream_base_url="https://api.openai.com",
    archive_dir="reports/run-001",
    run_id="run-001",
)
base_url = proxy.start()

# Route the stock CLI through the proxy (no fork):
#   OPENAI_BASE_URL={base_url}/v1   (or the CLI's base-url config key)
# ... run the agent to completion ...

proxy.stop()

index = TreeIndex(variant_root, distractor_paths=manifest_paths)
attributions = [
    index.classify_request_payload((proxy.archive_dir / r.payload_path).read_bytes())
    for r in proxy.records
]
trajectory = analyze_run(proxy.records, attributions)
trajectory.growth_shape                    # H2: gradual / step / plateau / sawtooth
trajectory.share_delta_late_minus_early    # H2 threshold input (§7.5)
```

## Honesty notes (mirrored in design.md)

- **Provider `usage` is the only authoritative token count.** Attribution
  splits it; `reconcile_with_usage` guarantees attributed tokens never exceed
  measured tokens. Attribution itself is a *lower bound* (paraphrased or
  truncated content does not match the line index).
- **SSE responses are buffered, not streamed through.** Capture fidelity and
  response content are preserved; streaming latency lands in
  `wall_clock_seconds` (secondary metric). Pass-through streaming is a TODO.
- **The proxy only sees what is routed through it.** The run-environment
  freeze (design §8.1.1) must lock network egress to the proxy for the record
  to be complete by construction; `session_parser.reconcile` flags traffic
  that bypassed it.

## Tests

```bash
cd research/repo-bloat-benchmark
python3 -m pytest harness/context_snapshots/tests/ -q
```

No external dependencies (stdlib + pytest only).
