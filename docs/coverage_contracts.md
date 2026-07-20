# Contract coverage matrix (`pdd checkup coverage`)

Build an inspectable rule-to-evidence matrix for `.prompt` files that define `<contract_rules>`.
No LLM required — pure static analysis.

Coverage is exposed via checkup:

```bash
pdd checkup coverage prompts/refund_payment_python.prompt
```

---

## Quick start

```bash
# Single file
pdd checkup coverage prompts/refund_payment_python.prompt

# Directory (scans recursively, skips *_LLM.prompt)
pdd checkup coverage prompts/

# JSON output for CI
pdd checkup coverage --json prompts/

# Custom story and test directories
pdd checkup coverage \
    --stories-dir user_stories \
    --tests-dir   tests \
    prompts/refund_payment_python.prompt

# Alias: --stories
pdd checkup coverage --stories user_stories prompts/
```

Default directories:
- `--stories-dir` defaults to `user_stories/`
- `--tests-dir` defaults to `tests/`
- `TARGET` argument defaults to `prompts/`

Runnable demo files live in `examples/coverage_contracts_demo/`:

```bash
pdd checkup coverage \
  --stories-dir examples/coverage_contracts_demo/user_stories \
  --tests-dir examples/coverage_contracts_demo/tests \
  examples/coverage_contracts_demo/prompts/refund_payment_python.prompt
```

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

## Canonical rule IDs

Contract declarations and evidence references accept these explicit ID families:

- `R1` and `R-1`
- `RULE1` and `RULE-1`
- Any of the above followed by one ASCII letter suffix, such as `R1a`,
  `R-1A`, `RULE1b`, or `RULE-1B`

IDs are normalized to uppercase. A suffix is part of the identity, so `R1` and
`R1A` are distinct rules; neither is collapsed into the other. The full grammar
is used by `<contract_rules>`, `<coverage>`, story `## Covers` references, and
prompt-qualified test references. The convenient unqualified shorthands use the
`R` family: function names use undashed IDs such as `test_R1a_*`, while comments
and docstrings accept `R1a` or `R-1A` forms.

---

## Story regression coverage (`has_regression_test`)

The rule statuses above are **rule-keyed** and derive from the `test_R<n>[suffix]`
naming heuristic (see "Test file heuristic" below). Story-regression coverage is
a separate, **story-keyed** dimension and does not change those statuses.

A user story (`user_stories/story__<slug>.md`) is "regression-backed" when at
least one collected pytest test claims it with the
`@pytest.mark.story(story_id="<slug>")` marker (see
[`docs/generating_user_stories.md`](generating_user_stories.md), "Story
regression tests"). `pdd checkup coverage` surfaces this per story as
`has_regression_test` plus a `status`:

| `has_regression_test` | Meaning |
|-----------------------|---------|
| `true` | One or more marker-linked pytest tests exist for the story |
| `false` | The story has no executable regression test (a gap to close) |

| `status` | Meaning |
|----------|---------|
| `story-regression-present` | A fresh, marker-linked test exists for the story (its recorded story hash matches the current one, or the marker is a legacy hashless traceability-only link). This is a presence/freshness verdict, not an execution result: pass/fail is verified separately by the story lane (`pytest -m story`). |
| `story-regression-missing` | No marker-linked test claims the story |
| `story-regression-stale` | A marker-linked test exists, but it was generated from an older story hash |

Use `pdd checkup coverage --story-regression-gate strict <target>` to fail on
missing or stale story regressions. The default `warn` mode reports the status
without changing the exit code; `off` leaves the status in JSON/output but does
not gate on it.

Two orphan conditions are reported as diagnostics, not gaps:

- **Story with no claiming test** — `has_regression_test: false` (the headline gap).
- **Test claiming a nonexistent story** — a marker references a `story_id` with no
  matching `story__<story_id>.md`; surfaced as a validation warning.

This dimension is additive and orthogonal to `story-only` / `test-only`, which
remain keyed off `test_R<n>` references.

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

Story files (`story__*.md`) are scanned **recursively** in `--stories-dir` (alias `--stories`).
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

Stories **without** `<!-- pdd-story-prompts: ... -->` apply to the prompt set under evaluation (same convention as `pdd/user_story_tests.py`). Stories **with** metadata are scoped to the listed prompt filenames or paths.

Path-qualified identities are exact after case and path-separator
normalization. For example, `prompts/a/foo.prompt` and
`prompts/b/foo.prompt` remain different prompts even though their basenames
match. A wrong qualified path never falls back to `foo.prompt`.

For compatibility, a basename-only reference such as `foo.prompt` may resolve
when that basename identifies exactly one prompt inside the trusted project
root. If the basename is duplicated, or the scanner cannot prove the complete
project boundary, basename fallback fails closed and contributes no evidence.
Metadata ownership and `## Covers` ownership are evaluated independently: valid
legacy metadata does not authorize a mismatched qualified Covers entry.

### 3. Test file heuristic

Test files (`test_*.py`) are scanned **recursively** in `--tests-dir` using a conservative heuristic.
Only `test*` functions that **explicitly reference a rule ID** are counted.

**Single-prompt runs** accept unqualified references (for example `test_R1_rejects_zero`).

**Directory runs** require **prompt-qualified** references so one shared `R1` on two prompts cannot mark both as covered from a single test. Use a docstring or signature line such as:

```python
def test_only_foo():
    """prompts/refund_payment_python.prompt#R1a: covers rule"""
```

Qualified references use the normalized project-relative prompt path. A
basename-only form is accepted only under the same unique, trusted-project
fallback described for stories. Directory scans therefore do not attribute a
generic `test_R1_*` function—or a reference to another same-basename prompt—to
every module declaring `R1`.

**Recognised patterns (documented heuristic):**

The unqualified patterns below apply to single-prompt scans. Directory scans
accept the prompt-qualified signature/docstring form shown above.

| Pattern | Example | Notes |
|---------|---------|-------|
| Function name | `def test_R1a_rejects_zero():` | Case-insensitive; maps to `R1A` |
| Inline comment | `def test_foo():  # R3a: covers rule` | On or immediately after the function definition |
| Inline comment | `def test_foo():  # covers R3a` | `covers R<ID>` or `rule R<ID>` prefix |
| Docstring first line | `"""R5a: validates boundary."""` | First 120 chars; `:` or `-` makes the reference explicit |

Functions that do **not** start with `test` are ignored entirely.
No semantic analysis of test logic is performed.

Syntax validation is deterministic. In a prompt-qualified directory scan, an
unparseable file marks a rule `failed` only when an actual `def test_*` or
`async def test_*` signature/first docstring line carries the matching qualified
reference. A marker in an unrelated module constant, arbitrary string, or
assignment after a malformed definition is not qualified evidence. Single-file
mode retains its broader backward-compatible unqualified scan.

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

## Python API and project roots

The underlying APIs are:

```python
build_coverage(
    path,
    stories_dir=None,
    tests_dir=None,
    *,
    prompt_text=None,
    require_prompt_qualified_tests=False,
    story_map=None,
    global_story_registry=None,
    project_root=None,
)

build_coverage_directory(
    directory,
    stories_dir=None,
    tests_dir=None,
    *,
    project_root=None,
)
```

`build_coverage_directory` recursively scans prompt files, skips
`*_LLM.prompt`, and enables prompt-qualified test evidence. It uses an explicit
`project_root` when supplied; otherwise it searches upward for a trusted project
marker such as `.git`, `.pdd`, `architecture.json`, or `pyproject.toml`. This is
important for nested layouts such as `pkg/prompts/`: the canonical identity is
`pkg/prompts/foo.prompt`, not merely `foo.prompt` or `prompts/foo.prompt`.

If no marker is discoverable, `build_coverage_directory` uses
`directory.parent` as its legacy scope. Pass `project_root` explicitly when the
prompt directory is nested more deeply or that parent is not the complete
project; direct single-file scans without a provable boundary disable basename
fallback rather than risk cross-package attribution.

---

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | All rules are `checked` or `waived`; no scanner read errors |
| `1` | Coverage gaps (`unchecked`, `story-only`, `test-only`, `failed`) and/or unreadable story/test files under the scan directories |
| `2` | Fatal error (missing `TARGET`, unreadable prompt file) |

Exit code `1` is intended for CI gating — teams can choose to enforce it or not.
Prompt-level failures use exit `2` so coverage gaps on other files are not masked in directory runs.

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

This means `pdd checkup coverage` is safe to run against any repository, even those that pre-date the contract rules convention.

---

## Pull request scope and dependencies

The coverage matrix (**#823**) is static analysis only; it does not call an LLM.

| Piece | Role | Required for #823? |
|-------|------|--------------------|
| `pdd checkup coverage` | Coverage CLI and `pdd/coverage_contracts.py` | **Yes** |
| `pdd contracts check` / `pdd checkup contract check` | Authoring lint for contract sections | **No** — optional companion |
| `pdd checkup lint` | Prompt/user-story quality lint | **No** |
| `pdd evidence` / `--evidence` manifests (#824) | Run audit receipts | **No** — separate feature |

Some PRs stack contract check, lint, coverage, and evidence for one review pass. That is a release convenience, not a runtime dependency.

---

## JSON schema

Coverage JSON is a single object envelope. **`pdd contracts check --json`** returns a
top-level **array** of contract-check results instead (one object per prompt/story scan).

```json
{
  "results": [
    {
      "path": "prompts/refund_payment_python.prompt",
      "has_contract_rules": true,
      "error": null,
      "read_errors": [],
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
| `error` | `string\|null` | Non-null if the prompt file could not be read (exit `2`) |
| `read_errors` | `list[string]` | Story/test files that could not be read under `--stories` / `--tests-dir` (exit `1`) |
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

Story-regression coverage is reported per **story** (not per rule) under a
`has_regression_test` boolean alongside the rule list, so the marker-keyed
dimension stays orthogonal to the rule `status` values above.

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
