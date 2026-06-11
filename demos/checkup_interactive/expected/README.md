# Expected Outcomes

Success criteria for the agentic checkup demo (issue #1423).

## Overall

```
bash demos/checkup_interactive/run_demo.sh --all
=== Summary ===
  PASS: 24   FAIL: 0
```

(The exact PASS count tracks the number of assertions; it must end `FAIL: 0`.)

## Per-prompt expected statuses (unified `--explain --json`)

| Prompt | lint | contract | coverage | gate | snapshot |
|--------|------|----------|----------|------|----------|
| 01_clean_task            | pass | pass | skip | skip | pass |
| 02_vague_clarification   | warn | pass | skip | skip | pass |
| 03_formatting_edge_case  | pass | pass | skip | skip | pass |
| 04_contract_sensitive    | warn | warn | warn | skip | pass |
| 05_coverage_sensitive    | pass | pass | warn | skip | pass |
| 06_snapshot_candidate    | pass | pass | skip | skip | fail |

## Agentic flow (deterministic / auto)

```
Starting agentic checkup session
Suggested plan: 1. lint  2. contract  3. coverage  4. gate  5. snapshot  6. drift
--- Checking: lint ---      ... contract ... coverage ... gate ... snapshot ... drift ---
[auto] [<finding-id>] <message> → <repair>          # auto mode only
Agentic checkup complete: <status> (N findings, M skipped, K auto-applied)
```

All six `Checking: <tool>` lines must appear — that is the proof the unified
agentic flow reaches every engine.

## LLM planner fallback

With no credential / no network:

```
WARNING: LLMPlanner: LLM call failed (...); falling back to deterministic.
Starting agentic checkup session
... Agentic checkup complete: ...
```

The command must **complete with exit 0** — it must not crash.

## Direct drift

```
PDD Drift Report: drift_candidate
Status: stable
```

## What indicates a broken integration

| Symptom | Likely cause |
|---------|-------------|
| `lint: pass` on `02_vague_clarification` | `scan_prompt` not reached by unified path |
| `coverage: skip` on `04_contract_sensitive` / `05_coverage_sensitive` | `build_coverage` not reached or rules not parsed |
| `snapshot: pass` on `06_snapshot_candidate` | `check_snapshot_policy` not reached or evidence found |
| Fewer than six `Checking:` lines | `CheckupAgent` not iterating `ALL_TOOLS` |
| `--planner llm` crashes with no key | `LLMPlanner` fallback broken |
| `--auto` blocks on a prompt | auto mode not bypassing the per-finding menu / plan confirm |
| `--interactive` (no `--auto`) succeeds without a TTY | TTY guard removed |
| `--apply` alone exits 0 | Click validation guard removed |
| Unified and direct differ on same prompt | Routing diverged from the shared abstraction layer |
