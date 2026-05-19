# Prompt Lint

`pdd prompt lint` checks prompt files and user stories for ambiguity that makes
requirements hard to test, implement, or formalize. Its default mode is
deterministic: it does not call an LLM, does not modify files, and is safe to
use in CI.

The command is about **prompt/story authoring quality**, not source-code lint.
For Python source lint command discovery, see `pdd/get_lint_commands.py`. For
contract rule structure and coverage, use `pdd contracts check` and
`pdd coverage --contracts`.

## Implementation Boundary

`pdd/prompt_lint.py` and `pdd/prompt_lint_pipeline.py` implement `pdd prompt lint`.
Product code and tests should use those modules and the single CLI command under
`pdd prompt`.

The LLM ambiguity prompt is `pdd/prompts/prompt_lint_LLM.prompt`. The
formalization coach prompt is `pdd/prompts/prompt_guidance_LLM.prompt`.
Keep this document synchronized with those `.prompt` files when changing
the authoring workflow, expected JSON fields, or clarify/coaching behavior.

`examples/prompt_lint_demo/` is the runnable demo for this workflow.

## One Command, Layered Depth

All authoring modes run through `pdd prompt lint`. Deterministic checks always
run first; pass `--ambiguity` for the LLM authoring workflow.

| Depth | Flags | LLM? | Purpose |
|-------|-------|------|---------|
| 0 — CI gate | *(none)* or `--strict` | No | Vague terms, missing vocabulary, weak outcomes, story criteria |
| 1 — Ambiguity review | `--ambiguity` | Yes | Advisory interpretations; auto coach + clarify when ambiguities are found |

The deterministic layer is the gate. LLM layers are local authoring aids only.

## Quick Start

```bash
# Scan one prompt file.
pdd prompt lint prompts/foo_python.prompt

# Scan all *.prompt files in a directory recursively.
pdd prompt lint prompts/

# Scan user stories.
pdd prompt lint --stories user_stories/

# Scan one prompt and a story directory together.
pdd prompt lint --stories user_stories/ prompts/foo_python.prompt

# Emit machine-readable JSON.
pdd prompt lint --json prompts/foo_python.prompt

# Treat warnings as errors for CI.
pdd prompt lint --strict prompts/foo_python.prompt

# LLM ambiguity review (coaching + clarification run automatically when needed).
pdd prompt lint --ambiguity prompts/foo_python.prompt

# Apply concrete vocabulary suggestions. Read-only unless --apply is passed.
pdd prompt lint --ambiguity --apply prompts/foo_python.prompt

# Accept LLM vocabulary suggestions without interactive prompts.
pdd prompt lint --ambiguity --non-interactive prompts/foo_python.prompt

# JSON includes results and guidance when ambiguities are found.
pdd prompt lint --ambiguity --json prompts/foo_python.prompt
```

## Paths

Example commands use paths relative to your repo. If a path is missing:

| Example path | Try instead |
|--------------|-------------|
| `prompts/refund_payment_python.prompt` | `tests/fixtures/contract_compile/refund_payment_python.prompt` |
| `prompts/foo_python.prompt` | `examples/prompt_lint_demo/prompts/payment_api_vague_python.prompt` |

## CI vs Authoring

| Context | Command |
|---------|---------|
| CI / pre-commit | `pdd prompt lint --strict <target>` |
| Local ambiguity review | `pdd prompt lint --ambiguity <target>` |

Do not pass `--ambiguity` in CI unless you explicitly want non-deterministic LLM
checks in that job.

Exit codes:

| Code | Meaning |
|------|---------|
| `0` | No issues |
| `1` | Warnings found |
| `2` | Errors found, or any issue with `--strict` |

## What It Checks

The deterministic linter checks prompt/story text for objective authoring
problems:

- known vague terms without vocabulary definitions
- acceptance criteria that depend on undefined terms
- contract rules or criteria with undefined vague terms but no observable outcome
- story `## Covers`, `## Glossary`, and `## Definitions` terms that can suppress warnings
- legacy safety: files without recognized contract/story sections do not fail

It does not judge whether the whole prompt is “good.” That broader guidance is
what the optional LLM review is for.

## What It Does Not Check

`pdd prompt lint` is not:

- a source-code linter like `ruff` or `mypy`
- a full contract structure validator
- a rule-to-test coverage matrix
- a formal verifier
- an LLM writing coach by default

Use related tools for those jobs:

| Need | Tool |
|------|------|
| Source-code lint commands | `pdd/get_lint_commands.py` and workflow lint steps |
| Contract rule syntax, rule IDs, modals, waivers | `pdd contracts check` |
| Rule/story/test coverage matrix | `pdd coverage --contracts` |
| LLM ambiguity, coaching, and clarification | `pdd prompt lint --ambiguity` |

## Argument Syntax

```text
pdd prompt lint [OPTIONS] [TARGET]
```

`TARGET` may be one `.prompt` file or a directory. Directories are scanned
recursively for `*.prompt` files.

`TARGET` is optional only when `--stories` is supplied.

`--stories` always takes a directory containing `story__*.md` files:

```bash
# Correct: --stories receives a story directory, TARGET receives the prompt.
pdd prompt lint --stories user_stories/ prompts/foo_python.prompt

# Wrong: --stories receives a prompt path.
pdd prompt lint --stories user_stories/prompts/foo_python.prompt
```

## Prompt And Markdown Scope

`pdd prompt lint` has two file scopes:

- `.prompt` files are scanned from `TARGET`.
- `story__*.md` files are scanned only from the directory passed to `--stories`.

Ordinary Markdown documentation such as `README.md`, PRDs, design docs, and this
file are not scanned by `pdd prompt lint` unless they are named `story__*.md`
inside the story directory. A prompt may still `<include>` Markdown docs for
generation or sync workflows, but prompt lint does not expand those includes and
does not try to keep included docs synchronized.

When `--ambiguity` writes accepted definitions, it writes to the scanned
`.prompt` file's `<vocabulary>` block. Story Markdown is used as lint input for
acceptance criteria and vocabulary sources (`## Covers`, `## Glossary`,
`## Definitions`); the current authoring write-back path is prompt-focused.

## Scanned Sections

Prompt files:

| Section | Purpose |
|---------|---------|
| `<contract_rules>` | Behavioral obligations |
| `<requirements>` | Functional requirements |
| `<acceptance_tests>` | Acceptance-test criteria |
| `%` prose lines | PDD prompt comments, only when the prompt also has a contract-like section |

Story files:

| Section | Purpose |
|---------|---------|
| `## Acceptance Criteria` | Story pass/fail criteria |

The following are intentionally not scanned as behavioral contract text:

```text
<pdd-reason>
<pdd-interface>
<pdd-dependency>
<waivers>
<deliverables>
<dependencies>
```

## Vocabulary Sources

Defined terms suppress vague-term warnings. The linter recognizes definitions
from:

| Source | Typical file |
|--------|--------------|
| `<vocabulary>` | `.prompt` files |
| `## Glossary` | story markdown |
| `## Definitions` | story markdown |
| `## Covers` | story markdown |

Definition extraction is intentionally generous. A definition like:

```text
- valid response: HTTP 200 with non-empty data
```

marks both `valid response` and `valid` as defined.

Cross-module story covers are also recognized:

```md
## Covers
- prompts/payment_python.prompt#R3: No provider call before validation
```

## Vague Terms

Default mode checks the core terms most likely to hide contract ambiguity:

```text
active
authorized
complete
duplicate
graceful
inactive
invalid
reasonable
recent
safe
successful
trusted
unauthorized
unsafe
untrusted
valid
```

`--strict` also checks broader words that can be noisy in normal prose:

```text
appropriate
correct
expected
incomplete
incorrect
necessary
normal
proper
sufficient
unexpected
```

Terms are matched as whole words. For example, deterministic mode catches
`graceful`, but not `gracefully`.

## Observable Outcomes

For `<contract_rules>`, `<acceptance_tests>`, and `## Acceptance Criteria`, the
linter adds a second warning when a line has an undefined vague term and no
observable outcome verb.

Observable verbs include common forms of:

```text
return, raise, write, emit, log, exit, reject, produce, store,
increment, decrement, set, clear, yield, throw, save, delete,
output, append, insert, update, remove, send, publish
```

Example:

```text
Only authorized users may call this endpoint.
```

This flags:

- `authorized` is undefined
- no observable outcome is stated

Better:

```text
When the caller lacks an unexpired token with scope="upload:write",
the endpoint MUST return HTTP 403 and MUST NOT write an upload record.
```

## Prompt Example

Problematic prompt:

```text
<contract_rules>
R1 - Upload validation
The service MUST accept valid uploads from active users.

R2 - Duplicate upload
Duplicate uploads must be rejected gracefully.
</contract_rules>
```

Deterministic findings:

- `valid` is undefined
- `active` is undefined
- `duplicate` is undefined
- `R1` has no precise observable outcome

Improved prompt:

```text
<vocabulary>
- valid upload: a file whose MIME type is in the allowlist and whose size is at most 10 MB
- active user: a user whose account.status field equals "active"
- duplicate upload: an upload whose tenant ID and SHA-256 hash match a previously accepted upload
</vocabulary>

<contract_rules>
R1 - Upload validation
When a request contains a valid upload from an active user,
the service MUST return HTTP 201 and MUST write one upload record.

R2 - Duplicate upload
When a request is a duplicate upload,
the service MUST return HTTP 409 and MUST NOT write a new upload record.
</contract_rules>
```

## Story Example

Problematic story:

```md
## Acceptance Criteria
- Given an authorized user uploads a valid file, then upload succeeds.
- Given a duplicate upload, then it is handled gracefully.
```

Improved story:

```md
## Acceptance Criteria
- Given a Bearer JWT with scope="upload:write" and exp in the future,
  when a user uploads a file whose MIME type is image/png and size is 2 MB,
  then the server returns HTTP 201 and writes one upload record.

- Given an upload whose tenant ID and SHA-256 hash match a previously accepted upload,
  when the same tenant submits it again,
  then the server returns HTTP 409 and writes no new upload record.

## Covers
- authorized user: a user with a Bearer JWT whose exp is in the future and whose scope includes "upload:write"
- valid file: a file whose MIME type is in the allowlist and whose size is at most 10 MB
- duplicate upload: an upload whose tenant ID and SHA-256 hash match a previously accepted upload
```

## JSON Output

```bash
pdd prompt lint --json prompts/foo_python.prompt
```

Output is a JSON array, one entry per scanned file:

```json
[
  {
    "path": "prompts/foo_python.prompt",
    "warn_count": 1,
    "error_count": 0,
    "issues": [
      {
        "level": "warn",
        "term": "valid",
        "section": "contract_rules",
        "line": "The service MUST accept valid uploads from active users.",
        "message": "Vague term \"valid\" used in [contract_rules] without a <vocabulary> definition.",
        "suggestion": "valid: <add a precise, observable definition here>",
        "interpretations": []
      }
    ]
  }
]
```

Deterministic findings always use an empty `interpretations` list. LLM findings
may populate it.

## Strict Mode

```bash
pdd prompt lint --strict prompts/foo_python.prompt
```

`--strict` does two things:

- escalates findings to errors
- enables the extended vague-term list

Use this for a hard CI gate when prompt ambiguity debt must be zero.

## Optional LLM Ambiguity Review

```bash
pdd prompt lint --ambiguity prompts/foo_python.prompt
```

The LLM pass is advisory. It can identify contextual ambiguity that deterministic
term matching cannot reliably catch:

- multi-word phrases such as `duplicate upload`
- weak definitions that exist but are still not precise
- bundled requirements that should be split
- missing fixtures, state, or oracle details in acceptance criteria

Example LLM output:

```text
Possible interpretations:
  1. Same filename
  2. Same file hash
  3. Same tenant ID and normalized file hash

Suggestion: Add to <vocabulary>:
  duplicate upload: an upload whose tenant ID and normalized file hash match a previously accepted upload
```

Important properties:

- `--ambiguity` enables the LLM pass; coaching and clarification follow automatically when ambiguities are found
- LLM failures are non-fatal
- deterministic lint remains the CI baseline
- LLM output should be reviewed by a human

## Formalization Coaching (automatic)

When the LLM ambiguity pass finds issues, coaching runs automatically before
clarification. If no ambiguous terms or phrases are found, coaching is skipped.

Coaching suggests:

- precise `<vocabulary>` additions
- formalizable `<contract_rules>` rewrites with stable IDs
- acceptance-criteria improvements with observable outcomes
- notes explaining why each change helps reproducibility or future formal verification

With `--json`, output includes both lint `results` and a `guidance` array:

```json
{
  "results": [],
  "guidance": [
    {
      "path": "prompts/foo_python.prompt",
      "summary": "The prompt needs clearer duplicate-upload semantics.",
  "vocabulary_suggestions": [
    {
      "term": "duplicate upload",
      "suggestion": "duplicate upload: an upload whose tenant ID and SHA-256 hash match a previously accepted upload",
      "why": "Defines the equality relation used by code and tests."
    }
  ],
  "rule_rewrites": [],
  "acceptance_criteria_improvements": [],
      "formalization_notes": [],
      "error": ""
    }
  ]
}
```

After coaching during authoring, run deterministic gates:

```bash
pdd prompt lint --strict prompts/foo_python.prompt
pdd contracts check prompts/foo_python.prompt
pdd coverage --contracts prompts/foo_python.prompt
pdd contracts compile --json prompts/foo_python.prompt
```

## Interactive Clarification (automatic)

After coaching, when ambiguities were found, the command prompts you to resolve
each term (unless `--non-interactive` or `--json` is set):

```bash
pdd prompt lint --ambiguity prompts/foo_python.prompt
pdd prompt lint --ambiguity --non-interactive prompts/foo_python.prompt
```

The clarification loop:

1. Runs the LLM ambiguity detector.
2. Shows each ambiguous term, possible interpretations, and suggested definition.
3. Lets the author accept, pick an interpretation, enter a custom definition, or skip.
4. Writes accepted definitions to `<vocabulary>`.
5. Reruns deterministic `prompt lint`, `contracts check`, and `contracts compile` summaries.

Use this when the LLM can identify ambiguity but only the author can choose the
intended meaning. `--non-interactive` accepts concrete LLM suggestions without
prompting, but it still writes only vocabulary definitions; it does not rewrite
contract rules.

Example interaction:

```text
Ambiguous term: duplicate upload
Possible interpretations:
  1. Same filename
  2. Same file hash
  3. Same tenant ID and normalized file hash
Suggested definition: duplicate upload: an upload whose tenant ID and normalized file hash match a previously accepted upload
Choose: [a]ccept suggestion, [p]ick interpretation, [e]dit, [s]kip
```

## Applying Suggestions

The linter is read-only by default.

```bash
pdd prompt lint --ambiguity --apply prompts/foo_python.prompt
```

`--apply` appends concrete suggestions to `<vocabulary>`, creating the block if
needed. Placeholder deterministic suggestions such as:

```text
valid: <add a precise, observable definition here>
```

are never written automatically.

## Formalizability Guidance

Prompt lint is not a formal verifier, but it helps make prompts formalizable.
A rule is easier to compile into tests or formal checks when it has:

- a stable rule ID
- defined domain terms
- a clear condition
- a modal verb (`MUST`, `MUST NOT`, `SHOULD`)
- an observable outcome
- explicit forbidden outcomes for negative rules

Weak:

```text
The system should handle recent duplicate uploads gracefully.
```

Better:

```text
R3 - Duplicate upload rejection
When an upload has the same tenant ID and SHA-256 hash as an accepted upload
created within the last 24 hours,
the service MUST return HTTP 409 and MUST NOT write a new upload record.
```

Use `pdd contracts check` for stricter contract syntax checks and
`pdd coverage --contracts` to see whether rule IDs are covered by stories,
tests, or waivers. Use `pdd contracts compile` when rules should become
machine-readable contract IR for future verification adapters.

## Fixtures

Runnable fixtures live under `tests/fixtures/prompt_lint/`:

| File | Purpose |
|------|---------|
| `vague_undefined.prompt` | Undefined vague terms |
| `vague_defined.prompt` | Same terms with vocabulary definitions |
| `clean.prompt` | Concrete prompt with no findings |
| `upload_handler_python.prompt` | Realistic vague upload handler |
| `upload_handler_with_vocab_python.prompt` | Upload handler with vocabulary |
| `story__vague_criteria.md` | Story with vague acceptance criteria |
| `story__covers.md` | Story with `## Covers` definitions |

Useful test command:

```bash
pytest tests/test_prompt_lint.py tests/commands/test_prompt.py tests/commands/test_prompt_comprehensive.py -q
```
