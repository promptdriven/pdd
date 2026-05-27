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
| `<vocabulary>` | Definitions that suppress vague-term warnings |
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

## Stretch goal (not in default CLI)

An optional LLM ambiguity pass exists in `contract_check.run_llm_ambiguity_pass` for future `--llm-ambiguity` wiring; it is not required for CI.
