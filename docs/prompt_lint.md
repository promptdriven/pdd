# Prompt lint for ambiguous contracts

`pdd prompt lint` checks prompt contracts and user-story acceptance criteria for
undefined vague terms. The default pass is deterministic, does not call an LLM,
and does not modify files — safe to use in CI.

## Quick start

```bash
# Scan one prompt file.
pdd prompt lint prompts/foo_python.prompt

# Scan all *.prompt files in a directory (recursive).
pdd prompt lint prompts/

# Scan a directory of user stories.
pdd prompt lint --stories user_stories/

# Scan a prompt and its stories together.
pdd prompt lint --stories user_stories/ prompts/foo_python.prompt

# Run the deterministic ambiguity pass explicitly.
pdd prompt lint --ambiguity prompts/foo_python.prompt

# Emit JSON (stdout only — informational messages go to stderr).
pdd prompt lint --json prompts/foo_python.prompt

# Escalate all warnings to errors (CI gate).
pdd prompt lint --strict prompts/foo_python.prompt

# Run the optional LLM ambiguity review.
pdd prompt lint --ambiguity --llm prompts/foo_python.prompt

# Write vocabulary suggestions back into the file.
pdd prompt lint --ambiguity --llm --apply prompts/foo_python.prompt
```

Exit codes:

| Code | Meaning |
|------|---------|
| `0`  | No issues |
| `1`  | Warnings present (and `--strict` not set) |
| `2`  | Errors present, OR any warning when `--strict` is set |

## Argument syntax

```
pdd prompt lint [OPTIONS] [TARGET]
```

`TARGET` is optional when `--stories` is supplied; required otherwise.
It may be a single `.prompt` file or a directory — directories are scanned
recursively for `*.prompt` files.

`--stories` always takes a **directory** of `story__*.md` files, never a
prompt path. Story files are scanned **recursively** — subdirectories are
included automatically. To scan both a prompt and stories together, keep them
as separate arguments:

```bash
# Correct — story directory after --stories, prompt as TARGET
pdd prompt lint --stories user_stories/prompt_lint_samples/ prompts/foo_python.prompt

# Wrong — passes the prompt path as the --stories value
pdd prompt lint --stories user_stories/prompt_lint_samples/prompts/foo_python.prompt
```

## Vague terms

The linter maintains hardcoded vocabularies of terms that are commonly
under-specified in contracts. Default mode checks this core list:

`active`, `authorized`, `complete`, `duplicate`, `graceful`, `inactive`, `invalid`,
`reasonable`, `recent`, `safe`, `successful`, `trusted`, `unauthorized`,
`unsafe`, `untrusted`, `valid`

`--strict` also checks this extended list:

`appropriate`, `correct`, `expected`, `incomplete`, `incorrect`, `necessary`,
`normal`, `proper`, `sufficient`, `unexpected`

Terms are matched as whole words. For example, `graceful` is checked, but the
word `gracefully` is not a match unless an LLM review flags it.

## Sections scanned

### Scanned sections (prompt files)

| Section tag | Example |
|-------------|---------|
| `<contract_rules>` | Numbered rules the implementation must satisfy |
| `<requirements>` | Bullet-point functional requirements |
| `<acceptance_tests>` | Explicit acceptance test criteria |
| `% prose lines` | Any line beginning with `%` (PDD comment convention) |

### Scanned sections (story / markdown files)

| Markdown heading | Example |
|------------------|---------|
| `## Acceptance Criteria` | Gherkin-style acceptance criteria |

### Not scanned (architecture metadata)

The following sections are intentionally excluded — they describe structure,
not observable behaviour, so vague terms inside them do not raise warnings:

`<pdd-reason>`, `<pdd-interface>`, `<pdd-dependency>`,
`<waivers>`, `<deliverables>`, `<dependencies>`

Prompts that contain none of the scanned sections (legacy format) produce zero
issues and are silently skipped.

## Vocabulary sources

Defining a term suppresses its warning wherever it appears in scanned sections.
Any of these sources are recognised:

| Source | Used in |
|--------|---------|
| `<vocabulary>` block | Prompt files |
| `## Glossary` heading | Story files |
| `## Definitions` heading | Story files |
| `## Covers` heading | Story files |

Term extraction is generous: when you define `valid response`, both the full
phrase `valid response` **and** the individual word `valid` are treated as
known, so a rule that uses `valid` anywhere is suppressed.

### Cross-module `## Covers` entries

Stories may reference rules from other prompt files using the `#rule-id`
format. The descriptive text after the colon is extracted as a known phrase:

```md
## Covers
- prompts/payment_python.prompt#R3: No provider call before validation
```

## Observable-outcome check

For `<contract_rules>`, `<acceptance_tests>`, and `## Acceptance Criteria`
sections only, the linter also checks whether each line that contains an
undefined vague term includes at least one observable outcome verb. If it does
not, an additional `(no observable outcome)` warning is emitted.

Observable outcome verbs include: `return`, `raise`, `write`, `emit`, `log`,
`exit`, `reject`, `produce`, `store`, `increment`, `decrement`, `set`, `clear`,
`yield`, `throw`, `save`, `delete`, `output`, `append`, `insert`, `update`,
`remove`, `send`, `publish` (and common inflections of each).

Note: `<requirements>` and `% prose` sections are scanned for vague terms but
do **not** trigger the observable-outcome check.

## Prompt example

```text
<contract_rules>
1. The function must return a valid response within a reasonable time.
2. Duplicate requests must be rejected gracefully.
3. Only authorized users may call this endpoint.
</contract_rules>

<requirements>
- Accept file uploads from active users only.
- Mark complete when all required fields are present.
</requirements>
```

Running `pdd prompt lint prompts/foo_python.prompt` against this produces:

- Warnings for `valid`, `reasonable`, `duplicate`, `authorized`, `active`, and
  `complete` (all undefined core vague terms).
- An extra `(no observable outcome)` warning for rule 3 — it uses `authorized`
  but has no observable verb such as `returns` or `rejects`.
- A `suggestion` entry for each term, ready to paste into `<vocabulary>`.

No warnings for rule 2 — `rejected` is an observable outcome verb, so the
observable-outcome check passes even though `duplicate` is still flagged as
vague. The word `gracefully` is not flagged by the deterministic default pass
because the core term is `graceful`.

### Fixing the warnings with `<vocabulary>`

```text
<vocabulary>
- valid response: HTTP 200 with a JSON body containing a non-empty "data" field
- reasonable time: completes within 500 ms at p99 under standard load
- duplicate request: a request whose idempotency key matches a previously accepted request within the last 24 hours
- graceful rejection: returns HTTP 409 with a JSON error body {"code":"DUPLICATE","message":"..."}
- authorized user: a user whose JWT token is present, unexpired, and carries the "write" scope
- active user: a user whose account.status field equals "active" in the accounts table
- complete: all required fields (name, email, role) are non-empty strings
</vocabulary>
```

After adding this block, the same prompt produces zero issues in default mode.

## Story example

```md
## Acceptance Criteria
1. Given an authorized user, when they upload a valid file, the server returns HTTP 201.
2. Given a duplicate upload, when submitted by the same tenant, the server returns HTTP 409.
3. Given an active user who has reached their limit, when they upload, the server returns HTTP 429.

## Covers
- authorized user: a user whose Bearer JWT is present, unexpired, and carries the "upload" scope
- valid file: a file whose MIME type is in the allowlist and whose size is ≤ 10 MB
- duplicate upload: an upload whose SHA-256 hash and tenant ID match a previously accepted upload
- active user: a user whose account.status field equals "active" in the accounts table
```

Running `pdd prompt lint --stories <directory-containing-this-story>` produces
zero issues in default mode — all core vague terms in the acceptance criteria
are defined in `## Covers`.

Without the `## Covers` section, `authorized`, `valid`, `duplicate`, and
`active` would each produce a warning.

## JSON output

```bash
pdd prompt lint --json prompts/foo_python.prompt
pdd prompt lint --json --stories user_stories/prompt_lint_samples/
```

Output is a JSON array. Each element corresponds to one file:

```json
[
  {
    "path": "prompts/foo_python.prompt",
    "warn_count": 7,
    "error_count": 0,
    "issues": [
      {
        "level": "warn",
        "term": "valid",
        "section": "contract_rules",
        "line": "1. The function must return a valid response within a reasonable time.",
        "message": "Vague term \"valid\" used in [contract_rules] without a <vocabulary> definition.",
        "suggestion": "valid: <add a precise, observable definition here>",
        "interpretations": []
      }
    ]
  }
]
```

`--json` writes only the JSON array to **stdout**; all informational messages
(e.g. update checks) go to **stderr**, so the output is safe to pipe or parse
without filtering.

## `--strict` mode

```bash
pdd prompt lint --strict prompts/foo_python.prompt
```

Escalates every warning to an error and exits with code 2 if any issue is
found. Use as a hard CI gate when you want to enforce zero vague-term debt.

## Optional LLM pass

The LLM pass is opt-in and requires both flags:

```bash
pdd prompt lint --ambiguity --llm prompts/foo_python.prompt
```

`--ambiguity` is valid by itself and runs the deterministic pass. The additional
LLM review is only run when both `--ambiguity` and `--llm` are supplied. Using
`--llm` without `--ambiguity` is an error.

The LLM pass may return richer suggestions and possible interpretations:

```text
Possible interpretations:
  1. Same filename
  2. Same file hash
  3. Same tenant ID and normalized file hash

Suggestion: Add to <vocabulary>:
  duplicate upload: an upload whose tenant ID and normalized file hash match a previously accepted upload
```

The `interpretations` field in JSON output is populated only by the LLM pass;
the deterministic pass always returns an empty array.

LLM failures are non-fatal — the deterministic pass remains the CI-safe
baseline.

## Applying suggestions (`--apply`)

The linter is read-only by default. Pass `--apply` to write suggestions back:

```bash
pdd prompt lint --ambiguity --llm --apply prompts/foo_python.prompt
```

`--apply` appends entries to the file's `<vocabulary>` block (creating one at
the end of the file if absent). It writes only **concrete** suggestions — LLM-
supplied definitions with real content. Placeholder suggestions from the
deterministic pass (`valid: <add a precise, observable definition here>`) are
shown for review but never written automatically.

`--apply` may be combined with or without `--llm`. Without `--llm`, the current
deterministic suggestions are placeholders, so nothing is written.

## Fixture files and demo

The repository ships runnable fixtures under `tests/fixtures/prompt_lint/`:

| File | Description |
|------|-------------|
| `vague_undefined.prompt` | Vague terms with no vocabulary — produces warnings |
| `vague_defined.prompt` | Same terms, all defined — produces zero issues |
| `clean.prompt` | Concrete, observable language throughout — zero issues |
| `upload_handler_python.prompt` | Real-world upload handler with flagged terms |
| `upload_handler_with_vocab_python.prompt` | Same handler with full vocabulary — zero issues |
| `story__vague_criteria.md` | Story with undefined vague acceptance criteria |
| `story__covers.md` | Same story with `## Covers` definitions — zero issues |

A standalone demo script is also available:

```bash
bash examples/prompt_lint_demo/demo.sh
```

The demo covers: deterministic prompt linting, vocabulary suppression, story
linting, JSON output, read-only guarantee, `--apply`, optional LLM review, and
strict mode.
