# PDD Contract Check

Deterministic lint for natural-language contract sections in `.prompt` files and
`story__*.md` user stories. No LLM calls in the default path — suitable for
local development and CI.

## Canonical command

**Primary (documented for new projects):**

```bash
pdd checkup contract check TARGET [OPTIONS]
```

**Backward-compatible alias** (matches [issue #822](https://github.com/promptdriven/pdd/issues/822)):

```bash
pdd contracts check TARGET [OPTIONS]
```

Both invoke the same engine (`pdd/contract_check.py`).

## Quick start

```bash
# Single prompt
pdd checkup contract check prompts/my_feature_python.prompt

# Directory of prompts
pdd checkup contract check prompts/

# Machine-readable output for CI
pdd checkup contract check --json prompts/

# Treat warnings as errors (exit code 2)
pdd checkup contract check --strict prompts/

# Also validate story ## Covers references
pdd checkup contract check prompts/ --stories stories/
```

## Sections parsed

When present in a prompt file:

| Section | Purpose |
|---------|---------|
| `<contract_rules>` | Testable rules with IDs and modal verbs |
| `<vocabulary>` | Definitions that suppress vague-term warnings (not `<covers>` / story `## Covers`) |
| `<capabilities>` | What the module may do |
| `<non_responsibilities>` | Explicit exclusions |
| `<coverage>` | Story/test/waiver evidence per rule ID |
| `<waivers>` | Formal waivers (`W1:`, expiry, approver) |

Legacy prompts **without** these sections are skipped (zero issues).

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | No errors and no warnings (or `--strict` with a clean run) |
| `1` | One or more **warnings** only |
| `2` | One or more **errors**, or any warning when `--strict` is set |

## Issue codes

| Code | Level | Description |
|------|-------|-------------|
| `DUPLICATE_ID` | error | Same rule ID appears twice in `<contract_rules>` |
| `MALFORMED_ID` | error | ID-like prefix that is not `R1` / `R-001` / `1.` style |
| `NON_SEQUENTIAL_ID` | warn | Gap in numeric rule IDs (e.g. R1 then R3) |
| `MISSING_MODAL` | warn/error | Rule or capability line lacks `MUST`, `MUST NOT`, `MAY`, `SHOULD`, `DOES NOT`, etc. |
| `VAGUE_TERM` | warn | Known vague phrase without a `<vocabulary>` entry |
| `UNKNOWN_COVERAGE_REF` | error | `<coverage>` cites a rule ID not in `<contract_rules>` |
| `UNCHECKED_RULE` | warn | Coverage line is `TODO` |
| `WAIVER_REF_MISSING` | error | `WAIVED W<n>` in coverage with no matching `<waivers>` block |
| `WAIVER_RULE_MISMATCH` | error | `WAIVED W<n>` in coverage cites a waiver whose `Rule:` does not match the coverage rule ID |
| `WAIVER_UNKNOWN_RULE` | error | Waiver `Rule:` references an ID not present in `<contract_rules>` |
| `MALFORMED_WAIVER_EXPIRES` | error | Waiver `Expires:` is present but not a parseable ISO date |
| `UNCOVERED_MUST_NOT` | warn | `MUST NOT` rule with no `<coverage>` entry |
| `MISSING_WAIVER_FIELDS` | warn | Waiver block missing Rule / Reason / Approved by / Expires |
| `EXPIRED_WAIVER` | warn | Waiver past its expiry date |
| `UNKNOWN_STORY_REF` | warn | Story `## Covers` references unknown rule ID |
| `UNKNOWN_TEST_REF` | warn | Coverage cites a `.py` path that does not exist |
| `PARSE_ERROR` / `FILE_NOT_FOUND` | error | Unreadable target file |

With `--strict`, all warnings are promoted to errors before exit.

## JSON output

`--json` prints a JSON array of result objects:

```json
[
  {
    "path": "prompts/foo_python.prompt",
    "warn_count": 0,
    "error_count": 1,
    "issues": [
      {
        "level": "error",
        "code": "DUPLICATE_ID",
        "rule_id": "R1",
        "section": "contract_rules",
        "line": "R1 - Example",
        "message": "...",
        "term": "",
        "suggestion": "...",
        "interpretations": []
      }
    ]
  }
]
```

JSON mode suppresses unrelated CLI noise on stdout (auto-update banners, etc.).

## Related commands

- **Architecture alignment:** `pdd checkup --validate-arch-includes`.
- **Contract coverage:** `pdd checkup coverage`.
- **Waiver policy gate:** `pdd checkup gate` (see below).

## Waiver policy gate (`pdd checkup gate`)

Enforce project policy on `<waivers>` blocks across prompt files. This is the
canonical gate command for issue #832 waiver workflows.

```bash
# Allow valid waivers (default)
pdd checkup gate prompts/

# Forbid any waiver
pdd checkup gate prompts/ --forbid-waivers

# Require every waiver to include a parseable Expires: date
pdd checkup gate prompts/ --require-expiration

# Fail on expired waivers
pdd checkup gate prompts/ --enforce-expiration

# Machine-readable output for CI
pdd checkup gate prompts/ --json
```

### Policy file

Read `gate.*` keys from `.pddrc` (or pass `--policy-file path/to/policy.yaml`):

```yaml
gate:
  allow_waivers: true
  forbid_waivers: false
  require_expiration: false
  enforce_expiration: true
```

When `--policy-file` is passed explicitly, a missing, unreadable, or malformed
file fails closed instead of falling back to permissive defaults.

CLI flags override file values. `--forbid-waivers` and `--no-allow-waivers`
both reject any waiver (`waivers-forbidden`). Malformed waivers and waivers
referencing unknown rule IDs always fail regardless of allow/forbid mode.

### Exit codes

| Code | Meaning |
|------|---------|
| `0` | No policy violations |
| `1` | One or more waiver policy violations |

JSON output shape: `{policy, waivers, violations, ok}`.

## Agentic evidence collector (not in default CLI)

An optional LLM-backed pass follows local import/wrapper chains to collect evidence for
effects that deterministic checks cannot resolve (e.g. `notificationClient.sendRefundNotice()`
resolving to `resend.emails.send()`).

```python
from pdd.agentic_reviewer import run_agentic_reviewer

findings = run_agentic_reviewer(
    contract_effects=[{"modal": "MUST_NOT", "action": "send email", "resource": "*"}],
    artifact_paths=["src/billing.ts", "clients/notificationClient.ts"],
    bounds={"max_files": 20, "max_follow_depth": 2,
            "max_search_results": 50, "max_runtime_seconds": 30},
)
```

Each finding carries `source: "agentic_reviewer"`, `severity: "warning"`,
a `confidence` float, `effect: {action, resource}`, supporting `evidence` excerpts, and
`agent_steps` for audit.  When evidence is insufficient the module returns
`{"judgment": "unknown", "confidence": 0.0}` rather than an empty list, so callers
can distinguish "no evidence found" from "no findings generated".

The reviewer is read-only (no network access, no code execution).  Bounds
(`max_files`, `max_follow_depth`, `max_search_results`, `max_runtime_seconds`) are
hard stops checked before each file read.  On invalid LLM JSON or LLM unavailability
the call degrades gracefully: no findings are emitted and no exception is raised.

The underlying hook point in the contract-check engine is
`contract_check.run_llm_ambiguity_pass`; the `--llm-ambiguity` CLI flag is not
yet wired to CI.
