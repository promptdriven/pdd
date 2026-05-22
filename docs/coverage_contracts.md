# `pdd coverage --contracts`

Build an inspectable rule-to-evidence matrix for `.prompt` files that define `<contract_rules>`.  
No LLM required — pure static analysis. Uses the shared IR from
[`pdd/contract_ir.py`](../pdd/contract_ir.py).

---

## Quick start

```bash
# Single file
pdd coverage --contracts prompts/refund_payment_python.prompt

# Directory (scans recursively, skips *_LLM.prompt)
pdd coverage --contracts prompts/

# JSON output for CI
pdd coverage --contracts --json prompts/

# Fail when MUST/MUST NOT rules are unchecked or evidence failed
pdd coverage --contracts --strict prompts/

# Custom story and test directories
pdd coverage --contracts \
    --stories-dir user_stories \
    --tests-dir   tests \
    prompts/refund_payment_python.prompt
```

Default directories:
- `--stories-dir` defaults to `user_stories/`
- `--tests-dir` defaults to `tests/`
- `TARGET` argument defaults to `prompts/`

Runnable fixtures live under `tests/fixtures/coverage_contracts/` and are used
by `tests/commands/test_coverage.py`.

---

## Example output

```
Prompt: prompts/refund_payment_python.prompt

Rule   Status       Stories                          Tests
──────────────────────────────────────────────────────────────────
R1     checked      story__refund_invalid.md         test_R1_rejects_zero_refund
R2     story-only   story__refund_invalid.md         -
R3     test-only    -                                test_R3_no_provider_call_invalid
R4     story-only   story__refund_idempotency.md     -
R5     unchecked    -                                -
R6     waived       story__secret_not_leaked.md      waiver: W1
R7     failed       story__refund_receipt.md         story__refund_receipt.md: missing ## Acceptance Criteria

  Summary: 2/7 rules fully covered (checked=1, waived=1, story-only=2, test-only=1, unchecked=1, failed=1)
```

---

## Status definitions

| Status | Condition |
|--------|-----------|
| `checked` | Has **both** story evidence AND test evidence |
| `story-only` | Story evidence present, no test evidence |
| `test-only` | Test evidence present, no story evidence |
| `unchecked` | No evidence at all (includes `TODO` entries in `<coverage>`) |
| `waived` | Explicitly waived via `WAIVED W<N>` in `<coverage>` or a matching `<waivers>` block |
| `failed` | A linked story or explicit test reference exists, but deterministic validation failed |

Waived rules are **never** flagged as gaps and do not affect the exit code.

---

## Evidence sources (priority order)

The engine collects evidence from four sources and classifies each rule accordingly:

### 1. `<coverage>` block (explicit summary)

If a prompt contains a `<coverage>` block, entries are treated as explicit evidence hints for that rule. Automatic story and test scans still run, so the matrix can reveal drift between the summary and the real files.

```
<coverage>
R1: story__refund_invalid.md, test_R1_rejects_zero_refund
R4: TODO add idempotency story
R6: WAIVED W1
</coverage>
```

- `WAIVED W<N>` → status `waived`
- Text starting with `TODO` → `unchecked` (placeholder, not evidence)
- Any other non-empty text → interpreted as additional evidence

### 2. Story `## Covers` sections

Story files (`story__*.md`) are scanned **recursively** in `--stories-dir`.  
A story is linked to a prompt if it contains:

```markdown
<!-- pdd-story-prompts: refund_payment_python.prompt -->
```

Within a linked story, the `## Covers` section lists the rules it addresses:

```markdown
## Covers

- R1: zero-amount refund is rejected before processing
- R2: over-refund amount is rejected before processing
```

Cross-module format is also supported:

```markdown
- prompts/refund_payment_python.prompt#R3: description
```

Stories without a `<!-- pdd-story-prompts: ... -->` comment are **not** linked to any prompt and are skipped.

### 3. Test file heuristic

Test files (`test_*.py`) are scanned **recursively** in `--tests-dir` using a conservative heuristic.  
Only `test*` functions that **explicitly reference a rule ID** are counted.

**Recognised patterns (documented heuristic):**

| Pattern | Example | Notes |
|---------|---------|-------|
| Function name | `def test_R1_rejects_zero():` | Case-insensitive: `test_r1_` also matches |
| Inline comment | `def test_foo():  # R3: covers rule` | Anywhere on the function definition line |
| Inline comment | `def test_foo():  # covers R3` | `covers R<N>` or `rule R<N>` prefix |
| Docstring first line | `"""R5: validates boundary."""` | First 120 chars of the docstring |

Functions that do **not** start with `test` are ignored entirely.  
No semantic analysis of test logic is performed.

Syntax validation is deterministic: if a `test_*.py` file cannot be parsed and it explicitly references `R<N>`, those rules are classified as `failed`.

### 4. `<waivers>` block

If a `<waivers>` block names a rule, that rule is classified as `waived` regardless of other evidence.

```
<waivers>
W1:
  Rule: R6
  Approved by: Security team (2025-12-01)
  Rationale: Provider SDK handles all secret material.
  Expires: 2026-12-01
</waivers>
```

### 5. Deterministic failed evidence

The v1 command does not call an LLM and does not execute pytest. It still reports `failed` when static evidence is internally invalid:

- A linked story covers a rule but has no `## Acceptance Criteria`.
- A `test_*.py` file has a Python syntax error and explicitly references the rule ID.

Failed rules are gaps and make the command exit `1`, the same as `unchecked`, `story-only`, and `test-only`.

---

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | All rules are `checked` or `waived` |
| `1` | At least one rule is `unchecked`, `story-only`, `test-only`, or `failed` |
| `2` | Error (file not found, unreadable prompt) |

Exit code `1` is intended for CI gating — teams can choose to enforce it or not.

---

## Legacy-safe guarantee

Prompts that do **not** contain a `<contract_rules>` section produce:

```
Prompt: prompts/legacy_utility_python.prompt
  No <contract_rules> section — no contract coverage data.
```

- Exit code `0`
- No rules reported
- No errors raised

This means `pdd coverage --contracts` is safe to run against any repository, even those that pre-date the contract rules convention.

---

## JSON schema

```json
{
  "results": [
    {
      "path": "prompts/refund_payment_python.prompt",
      "has_contract_rules": true,
      "error": null,
      "rules": [
        {
          "rule_id": "R1",
          "status": "checked",
          "stories": ["story__refund_invalid.md"],
          "tests": ["test_R1_rejects_zero_refund"],
          "waiver": null,
          "failures": []
        },
        {
          "rule_id": "R6",
          "status": "waived",
          "stories": [],
          "tests": [],
          "waiver": "W1",
          "failures": []
        }
      ],
      "summary": {
        "total": 6,
        "checked": 1,
        "story_only": 2,
        "test_only": 1,
        "unchecked": 1,
        "waived": 1,
        "failed": 0
      }
    }
  ],
  "total_prompts": 1,
  "prompts_with_contracts": 1
}
```

### Top-level fields

| Field | Type | Description |
|-------|------|-------------|
| `results` | `list` | One entry per prompt file scanned |
| `total_prompts` | `int` | Total number of prompt files processed |
| `prompts_with_contracts` | `int` | Count of prompts that have a `<contract_rules>` section |

### Result fields

| Field | Type | Description |
|-------|------|-------------|
| `path` | `string` | Absolute or relative path to the prompt file |
| `has_contract_rules` | `bool` | `false` for legacy prompts |
| `error` | `string\|null` | Non-null if the file could not be read |
| `rules` | `list[Rule]` | Coverage entry per rule |
| `summary` | `object` | Per-status counts |

### Rule fields

| Field | Type | Description |
|-------|------|-------------|
| `rule_id` | `string` | Normalised rule ID, e.g. `"R1"` |
| `status` | `string` | One of `checked`, `story-only`, `test-only`, `unchecked`, `waived` |
| `stories` | `list[string]` | Filenames of stories that cover this rule |
| `tests` | `list[string]` | Names of test functions that reference this rule |
| `waiver` | `string\|null` | Waiver ID (e.g. `"W1"`) if waived, else `null` |
| `failures` | `list[string]` | Deterministic story/test validation failures for `failed` rules |

---

## Prompt format reference

```
<contract_rules>
R1 - Short name

For every <entity/action>,
the system MUST <observable behavior>
when <condition>.

R2 - Another rule
The system MUST NOT <forbidden outcome>.
</contract_rules>

<vocabulary>
refund amount: the monetary value to be returned; must be positive
</vocabulary>

<coverage>
R1: story__refund_invalid.md, test_R1_rejects_zero
R2: TODO add over-refund story
R6: WAIVED W1
</coverage>

<waivers>
W1:
  Rule: R6
  Approved by: Security (2025-12-01)
  Rationale: SDK handles secrets; service never sees raw credentials.
  Expires: 2026-12-01
</waivers>
```

---

## Alignment with the prompting guide

- Story `## Covers` is the primary evidence source, matching the guide's
  story-driven validation model (see `docs/prompting_guide.md`, "Story Covers").
- The `<coverage>` block is an optional summary — it does not replace stories or tests.
- `<waivers>` handles exceptions explicitly, avoiding silent unchecked rules.
- Prompts without `<contract_rules>` are never hard-failed (legacy-safe by design).
- The test heuristic is conservative and fully documented; no semantic inference is performed.
