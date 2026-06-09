# Expected Outcomes

Success criteria for `bash demos/checkup_interactive/run_demo.sh --all`.

## Overall

```
=== Results: 21 passed, 0 failed ===
```

## Per-check expected statuses

| Prompt | lint | contract | coverage | gate | snapshot |
|--------|------|----------|----------|------|----------|
| 01_clean_task | pass | pass | skip | skip | pass |
| 02_vague_requirements | warn | pass | skip | skip | pass |
| 03_contract_coverage | warn | warn | warn | skip | pass |
| 04_formatting_edge_case | pass | pass | skip | skip | pass |
| 05_snapshot_candidate | pass | pass | skip | skip | fail |

## What indicates a broken integration

| Symptom | Likely cause |
|---------|-------------|
| `lint: pass` on `02_vague_requirements` | `scan_prompt` not reached by unified path |
| `coverage: skip` on `03_contract_coverage` | `build_coverage` not reached or R901-R903 not parsed |
| `snapshot: pass` on `05_snapshot_candidate` | `check_snapshot_policy` not reached or evidence found |
| `requires_clarification` missing from lint findings | `SourceSetFinding` model missing field |
| `requires_clarification: false` on all lint findings | `_requires_clarification()` logic broken |
| A1 exits 0 (`--apply` alone succeeds) | Click validation guard removed |
| A2 exits 0 (`--interactive` without TTY) | TTY guard removed |
| A3 produces non-JSON output | Exception escaping JSON serialisation |
| Unified and direct differ on same prompt | Routing diverged from shared abstraction layer |
