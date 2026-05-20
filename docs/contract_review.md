# `pdd contracts review --llm`

Advisory LLM review of the shared contract IR. **Not a CI gate** — human
decisions are recorded; rejection does not fail builds.

## Usage

```bash
pdd contracts review --llm prompts/foo_python.prompt
pdd contracts review --llm --coverage prompts/foo_python.prompt
pdd contracts review --llm --json prompts/foo_python.prompt
pdd contracts review --llm --interactive prompts/foo_python.prompt
```

## Separation from `pdd prompt lint`

| | `prompt lint --ambiguity` | `contracts review --llm` |
|--|---------------------------|---------------------------|
| Scope | Whole prompt, requirements, AC | Rules, vocabulary, coverage, waivers |
| Output | Vocabulary coaching | Rule-tied findings |
| CI | Optional | Never |

Use `pdd contracts check` for deterministic CI. Do not use
`contracts check --llm-ambiguity` in CI — prefer `contracts review --llm` locally.

## Human decisions

Interactive mode writes `<contract_review>`:

```xml
<contract_review>
LLM-A1:
  Rule: R1
  Status: rejected
  Reviewer: yifei
  Reason: Use idempotency key, not content hash.
  Date: 2026-05-19
</contract_review>
```

Decision memory: `.pdd/contract_review_decisions.json`

States: `accepted`, `accepted_with_edit`, `rejected`, `needs_more_info`,
`deferred`, `waived`, `escalated`, `superseded`

## CI policy

| Issue | Human rejects LLM | CI |
|-------|-------------------|-----|
| LLM-only finding | — | No impact |
| DUPLICATE_ID, etc. | — | Still fails |
| VAGUE_TERM | — | warn; error with `--strict` |
| Missing coverage | — | warn; error with `coverage --strict` |
