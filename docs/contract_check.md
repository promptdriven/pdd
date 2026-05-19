# Contract check for prompt authoring quality

`pdd contracts check` parses the structured contract sections of a prompt file
and reports structural authoring defects deterministically — no LLM required,
safe for CI.

## Quick start

```bash
# Check one prompt file.
pdd contracts check prompts/foo_python.prompt

# Check all *.prompt files in a directory (recursive).
pdd contracts check prompts/

# Emit JSON (stdout only — informational messages go to stderr).
pdd contracts check --json prompts/

# Treat all warnings as errors (CI hard gate).
pdd contracts check --strict prompts/foo_python.prompt

# Also validate story ## Covers rule-ID references.
pdd contracts check --stories user_stories/ prompts/foo_python.prompt

# Run optional LLM ambiguity review on <contract_rules> terms.
pdd contracts check --llm-ambiguity prompts/foo_python.prompt
```

Exit codes:

| Code | Meaning |
|------|---------|
| `0`  | No issues |
| `1`  | Warnings present (and `--strict` not set) |
| `2`  | Errors present, OR any warning when `--strict` is set |

## Sections parsed

The checker reads these XML-delimited sections when present in a prompt file:

| Section | What is checked |
|---------|-----------------|
| `<contract_rules>` | Rule IDs, modal verbs, vague terms |
| `<vocabulary>` | Term definitions that suppress vague-term warnings |
| `<capabilities>` | Modal verb presence on each capability line |
| `<coverage>` | Rule ID validity; MUST NOT rule coverage; waiver cross-references |
| `<waivers>` | Required fields; expiry dates |
| `<non_responsibilities>` | Parsed but not checked (informational only) |

Prompts that contain **none** of the checked sections (legacy format) produce
zero issues and are silently marked clean.

## Rule ID formats

Two canonical formats are accepted and may be mixed within a file:

```text
# Explicit R-prefix IDs (both short and zero-padded forms)
R1 - Short name
R-001: Description

# Sequential numeric IDs
1. Rule text
2. Rule text
```

Anything else that looks like an ID prefix but does not match (e.g. `R_001`,
`RR-01`, `RULE_1`) is flagged as `MALFORMED_ID`.

## Checks reference

### `DUPLICATE_ID` — error

The same rule ID appears more than once in `<contract_rules>`.

```text
R2 - Merchant check
The system MUST only accept authorized merchants.

R2 - Payment validation        ← duplicate
The system MUST reject requests with an invalid payment method.
```

**Fix:** Assign each rule a unique ID.

---

### `MALFORMED_ID` — error

A line begins with something that resembles an ID prefix but does not match the
canonical `R<N>`, `R-<N>`, `RULE<N>`, or `<N>.` formats.

```text
R_001: Rule text          ← underscore separator
RR-01: Rule text          ← double-letter prefix
RULE_003: Rule text       ← underscore
```

**Fix:** Use `R1 -`, `R1:`, `R-001:`, or plain `1.` sequential numbering.

---

### `NON_SEQUENTIAL_ID` — warning

Explicit `R<N>` IDs have a numeric gap, suggesting a rule was deleted or
misnumbered. This is a warning, not an error, because intentional gaps are
sometimes used to match external specification numbering.

```text
R1, R2, R4   ← R3 is missing
```

**Fix:** Renumber rules sequentially, or add a comment explaining the gap.

---

### `MISSING_MODAL` — warning (error in `--strict`)

A `<contract_rules>` block or `<capabilities>` line contains no recognised
modal verb.

Required modals: `MUST`, `MUST NOT`, `MAY`, `MAY NOT`, `SHOULD`, `SHOULD NOT`,
`SHALL`, `SHALL NOT`, `DOES NOT`.

```text
R4 - Fraud gate
The system reject suspicious transactions.    ← no modal verb
```

**Fix:** Add a modal: `"The system MUST NOT process suspicious transactions."`

---

### `VAGUE_TERM` — warning

A line in `<contract_rules>` uses a known vague phrase without a matching
`<vocabulary>` definition. The same core term list as `pdd prompt lint` is used:

`active`, `authorized`, `complete`, `duplicate`, `graceful`, `inactive`,
`invalid`, `reasonable`, `recent`, `safe`, `successful`, `trusted`,
`unauthorized`, `unsafe`, `untrusted`, `valid`

```text
R6 - Error format
The system MUST return a reasonable error response within a reasonable time.
                          ↑ vague, no <vocabulary> entry
```

**Suppression:** Define the term in `<vocabulary>` to silence the warning:

```text
<vocabulary>
- reasonable response time: completes within 500 ms at p99 under standard load
</vocabulary>
```

Term matching is generous — defining `valid file` suppresses warnings for both
`valid file` and the bare word `valid`.

---

### `UNKNOWN_COVERAGE_REF` — error

A `<coverage>` entry cites a rule ID that does not exist in `<contract_rules>`.

```text
<coverage>
- R3: test_burst_window (tests/test_rate_limiter.py)   ← R3 not defined
</coverage>
```

**Fix:** Add the missing rule to `<contract_rules>`, or remove the stale
coverage entry.

---

### `UNCHECKED_RULE` — warning

A `<coverage>` entry is marked `TODO`, meaning no test, story, or waiver has
been assigned yet.

```text
<coverage>
- R4: TODO add integration test
</coverage>
```

**Fix:** Replace `TODO` with a test name, story filename, or `WAIVED W<N>`.

---

### `UNCOVERED_MUST_NOT` — warning

A `MUST NOT` rule has no entry in `<coverage>`. This check only fires when a
`<coverage>` section is present at all (so legacy prompts without `<coverage>`
are unaffected).

`MUST NOT` rules carry the highest risk — a missing or incorrect implementation
silently violates a prohibition. Requiring coverage evidence surfaces this
early.

```text
<contract_rules>
R5 - Raw card data
The system MUST NOT store raw card numbers.    ← no coverage entry
</contract_rules>

<coverage>
- R1: …
- R3: …
# R5 absent
</coverage>
```

**Fix:** Add a coverage entry: `R5: test_no_raw_card_stored (tests/test_payment.py)`,
a story reference, or `WAIVED W<N>`.

---

### `WAIVER_REF_MISSING` — error

A `<coverage>` entry cites `WAIVED W<N>`, but `<waivers>` has no corresponding
block for that waiver ID.

```text
<coverage>
- R4: WAIVED W2    ← W2 not defined in <waivers>
</coverage>
```

**Fix:** Add a `W2:` block to `<waivers>`, or change the coverage evidence to a
test or story.

---

### `MISSING_WAIVER_FIELDS` — warning

A `<waivers>` block is missing one or more required fields.

Required fields: `Rule`, `Reason`, `Approved by`, `Expires`.

```text
<waivers>
W1:
  Rule: R4
  Reason: Pending access-control overhaul.
  # Missing: Approved by, Expires
</waivers>
```

**Fix:** Add all required fields:

```text
W1:
  Rule: R4
  Status: temporary
  Reason: Pending access-control overhaul in Q3.
  Approved by: security-team
  Expires: 2026-12-31
  Follow-up: Implement fine-grained scope checks (issue #712).
```

---

### `EXPIRED_WAIVER` — warning

A waiver's `Expires` date is in the past.

**Fix:** Extend the expiry date, add a test or story to close the waiver, or
remove it if the rule is now fully covered.

## Full prompt example

```text
<vocabulary>
- authorized merchant: a merchant whose API key is present, unexpired, and has
  the "payments:write" scope verified against the OAuth2 provider
- duplicate charge: a charge whose idempotency_key matches an existing charge
  created within the last 24 hours by the same merchant
- suspicious transaction: a transaction whose risk_score exceeds 0.85
</vocabulary>

<contract_rules>
R1 - Idempotency guard

For every POST /charges request,
the system MUST reject duplicate charges
when the idempotency_key matches an existing charge within 24 hours.

This rule is violated if the system creates a second charge row.

R2 - Merchant authorization
The system MUST only accept requests from authorized merchants.

R3 - Fraud gate
The system MUST NOT process suspicious transactions.
</contract_rules>

<coverage>
- R1: test_duplicate_charge_rejected (tests/test_payment.py)
- R2: test_unauthorized_merchant_rejected (tests/test_payment.py)
- R3: test_suspicious_transaction_blocked (tests/test_payment.py)
</coverage>

<capabilities>
- MUST NOT store raw card numbers; only vaulted tokens are permitted.
- MAY retry vault service calls up to two times before returning HTTP 503.
</capabilities>

<non_responsibilities>
- Currency conversion.
- PCI DSS key management (handled by the vault service).
</non_responsibilities>
```

Running `pdd contracts check` against this produces zero issues.

## JSON output

```bash
pdd contracts check --json prompts/foo_python.prompt
pdd contracts check --json prompts/
```

Output is a JSON array. Each element corresponds to one file:

```json
[
  {
    "path": "prompts/payment_python.prompt",
    "warn_count": 1,
    "error_count": 1,
    "issues": [
      {
        "level": "error",
        "code": "DUPLICATE_ID",
        "rule_id": "R2",
        "section": "contract_rules",
        "line": "R2 - Payment validation",
        "message": "Rule ID \"R2\" appears more than once in <contract_rules>.",
        "term": "",
        "suggestion": "Assign a unique ID to each rule. Rename or remove the duplicate.",
        "interpretations": []
      }
    ]
  }
]
```

`--json` writes only the JSON array to **stdout**; all informational messages
go to **stderr**, so the output is safe to pipe or parse without filtering.

## `--strict` mode

```bash
pdd contracts check --strict prompts/foo_python.prompt
```

Escalates every warning to an error and exits with code 2 if any issue is
found. Use as a hard CI gate when you want to enforce zero contract-authoring
debt. `MISSING_MODAL` in particular is normally a warning but becomes an error
under `--strict`.

## Story `## Covers` validation

```bash
pdd contracts check --stories user_stories/ prompts/foo_python.prompt
```

`--stories` takes a **directory** of `story__*.md` files. The checker scans
each story's `## Covers` section and validates that every rule ID referenced
there actually exists in the linked prompt's `<contract_rules>`.

Two reference formats are supported:

```md
## Covers

# Single-prompt format — validates against the TARGET prompt
- R1: idempotency_key uniqueness enforced within 24-hour window
- R3: suspicious transaction risk_score exceeds 0.85 threshold

# Cross-module format — validates against the named prompt file
- prompts/payment_python.prompt#R2: authorized merchant holds valid API key
```

Stories referenced from `--stories` are scanned recursively — subdirectories
are included automatically.

## Waivers

`<waivers>` blocks document exceptions to `MUST NOT` rules that cannot be
covered by tests or stories in the current release cycle.

```text
<waivers>
W1:
  Rule: R4
  Status: temporary
  Reason: Read-only admin endpoints exempt pending Q3 access-control overhaul.
  Approved by: security-team
  Expires: 2026-12-31
  Follow-up: Implement fine-grained scope checks (issue #712).
</waivers>
```

Reference the waiver in `<coverage>` to suppress `UNCOVERED_MUST_NOT`:

```text
<coverage>
- R4: WAIVED W1
</coverage>
```

Required waiver fields: `Rule`, `Reason`, `Approved by`, `Expires`.
Optional fields: `Status`, `Follow-up`.

## Optional LLM pass

```bash
pdd contracts check --llm-ambiguity prompts/foo_python.prompt
```

The LLM pass is opt-in. It reviews `<contract_rules>` terms for subtle
ambiguity beyond the deterministic vague-term list and may suggest richer
`<vocabulary>` definitions with possible interpretations:

```text
Possible interpretations:
  1. Requests with the same idempotency key in the header
  2. Requests with identical body content within 60 seconds
  3. Requests from the same user ID for the same resource within 5 seconds

Suggestion:
  duplicate charge: a charge whose idempotency_key matches an existing charge
  created within 30 seconds by the same merchant_id
```

LLM failures are non-fatal — the deterministic pass remains the CI-safe
baseline.

## Fixture files

The repository ships runnable fixtures under `tests/fixtures/contract_check/`:

| File | Description |
|------|-------------|
| `valid_contract_python.prompt` | All sections well-formed — zero issues |
| `payment_api_clean_python.prompt` | Realistic payment API — fully specified, zero issues |
| `auth_service_clean_python.prompt` | Auth service with waivers — fully specified, zero issues |
| `duplicate_ids_python.prompt` | Duplicate R2 — triggers `DUPLICATE_ID` |
| `malformed_ids_python.prompt` | `R_001` prefix — triggers `MALFORMED_ID` |
| `non_sequential_ids_python.prompt` | R1, R2, R4 gap — triggers `NON_SEQUENTIAL_ID` |
| `missing_modal_python.prompt` | Rule without modal verb — triggers `MISSING_MODAL` |
| `vague_no_vocab_python.prompt` | Vague terms, no vocabulary — triggers `VAGUE_TERM` |
| `vague_with_vocab_python.prompt` | Same terms, all defined — zero issues |
| `unknown_coverage_refs_python.prompt` | Coverage cites R99 — triggers `UNKNOWN_COVERAGE_REF` |
| `uncovered_mustnot_python.prompt` | MUST NOT with no coverage — triggers `UNCOVERED_MUST_NOT` |
| `payment_api_issues_python.prompt` | Combined defects in one file (integration testing) |
| `rate_limiter_issues_python.prompt` | Sequential gap + coverage errors (integration testing) |
| `waiver_valid_python.prompt` | Complete, unexpired waiver — zero issues |
| `waiver_expired_python.prompt` | Expired waiver — triggers `EXPIRED_WAIVER` |
| `waiver_missing_fields_python.prompt` | Incomplete waiver — triggers `MISSING_WAIVER_FIELDS` |
| `legacy_no_sections_python.prompt` | No contract sections — silently clean |
| `story__covers_rule_ids.md` | Valid `## Covers` entries — zero issues |
| `story__unknown_rule_ids.md` | `## Covers` with unknown IDs — triggers `UNKNOWN_STORY_REF` |
| `story__payment_flow.md` | Realistic story with valid covers for payment API |
| `story__payment_bad_refs.md` | Story citing R99, R100 — triggers `UNKNOWN_STORY_REF` |
