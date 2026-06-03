# `pdd checkup` Advisory Layer (`--review off|explain`)

All local `pdd checkup` subcommands except `snapshot` accept a shared `--review` option that optionally appends a read-only LLM advisory pass after deterministic checks.

---

## Option Reference

| Value | Behavior |
|-------|----------|
| `--review off` | **Default.** No LLM call. Output is identical to current behavior. |
| `--review explain` | Run advisory LLM pass after deterministic checks; append `"advisory"` to JSON output. |

`--review` is **rejected** on `pdd checkup snapshot` with a usage error — snapshot policy is purely deterministic.

---

## Advisory Invariant

**Deterministic checks always run first and alone control exit codes.**

The advisory pass:
- Runs after all local heuristic checks complete.
- NEVER changes the exit code, even if the LLM returns findings.
- On LLM failure (API error, timeout, missing credentials): sets `advisory.status="failed"`, adds one finding with the error message, and continues. Exit code is unchanged.

---

## JSON Output Schema

When `--review explain` is active, a `"advisory"` key is added to JSON output.
When `--review off` (default), no `"advisory"` key is present.

### `CheckupReport` shape

```json
{
  "status": "ok",
  "findings": [
    {
      "severity": "warn",
      "area": "contract_rules",
      "message": "Human-readable finding text.",
      "evidence": "Optional supporting evidence snippet."
    }
  ]
}
```

### `status` values

| Value | Meaning |
|-------|---------|
| `"skipped"` | `--review off`; LLM was not called. |
| `"ok"` | LLM ran; no advisory findings. |
| `"warned"` | LLM ran; one or more findings returned. |
| `"failed"` | LLM call failed (API error, missing credentials, timeout). |

### Injection pattern by command

| Command | JSON payload type | Advisory injection |
|---------|-------------------|--------------------|
| `checkup lint` | Array of result objects | Per-item sibling key `"advisory"` |
| `checkup contract check` | Array of result objects | Per-item sibling key `"advisory"` |
| `checkup coverage` | Envelope `{results, total_prompts, ...}` | Top-level sibling key `"advisory"` |
| `checkup gate` | Dict `{passed, exit_code, ...}` | Top-level sibling key `"advisory"` |
| `checkup drift` | Dict (report) | Top-level sibling key `"advisory"` |

---

## `pdd/checkup_advisory.py` API

The `pdd.checkup_advisory` module provides lightweight shared dataclasses:

```python
from pdd.checkup_advisory import (
    CheckupFinding,   # dataclass: severity, area, message, evidence=""
    CheckupReport,    # dataclass: status, findings
    SKIPPED_REPORT,   # constant: CheckupReport(status="skipped", findings=[])
    failed_report,    # failed_report(message: str) -> CheckupReport
    final_exit_code,  # final_exit_code(deterministic: int, report: CheckupReport) -> int
    report_as_dict,   # report_as_dict(report: CheckupReport) -> dict
)
```

`final_exit_code` always returns `deterministic` unchanged — it is an invariant assertion, not a transformation.

---

## `pdd/commands/checkup_review_options.py` API

The shared Click decorator and snapshot rejection helper:

```python
from pdd.commands.checkup_review_options import (
    review_option,             # Click decorator: adds --review off|explain
    reject_review_on_snapshot, # raises UsageError when review != "off"
)
```

Usage in a subcommand:

```python
@click.command("coverage")
@review_option
def coverage_cmd(review: str, ...) -> None:
    # review is "off" or "explain"
    ...
```

---

## Deprecation: `--llm` on `pdd checkup lint`

The `--llm` flag on `pdd checkup lint` is a **deprecated alias** for `--review explain`. It remains functional but emits a one-line deprecation warning on stderr:

```
DeprecationWarning: --llm is deprecated; use --review explain
```

It will be removed in a future release.

---

## Non-goals

- No `--review investigate` (follow-up issue in stack).
- No file mutation (`--apply`, `--dry-run` are reserved for a future write-layer issue).
- Advisory findings are NOT written to the evidence manifest (`.pdd/evidence/`).
