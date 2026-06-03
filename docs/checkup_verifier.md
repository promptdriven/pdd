# `pdd checkup` — Local Evidence & Contract Verifier

`pdd checkup` is a dual-mode command:

- **Mode A — Local evidence & contracts (this document):** Deterministic, fast, no LLM required. Run in CI or locally to verify prompt quality, coverage, and drift.
- **Mode B — Prompt coaching:** Interactive authoring loop against the contract schema. See [docs/checkup_prompt_coaching.md](checkup_prompt_coaching.md).
- **Mode C — Agentic issue / PR review:** Runs the full checkup orchestrator against a GitHub issue or PR. See `pdd checkup --help` (agentic section).

## Mental model

```
generate | sync | test | verify  →  action verbs (produce artifacts)
checkup                          →  verifier + coaching (inspect artifacts)
```

## Local verifier subcommands

| Subcommand | What it checks | LLM? |
|-----------|---------------|------|
| `pdd checkup lint TARGET` | Prompt and user-story quality, vague terms, vocabulary | No (optional `--llm`) |
| `pdd checkup contract check TARGET` | Contract section lint (`<contract_rules>`, `<coverage>`, waivers) | No |
| `pdd checkup coverage TARGET` | Rule-to-story/test coverage matrix | No |
| `pdd checkup gate [TARGET]` | Waiver policy gate, evidence manifest enforcement | No |
| `pdd checkup snapshot PROMPT_FILE` | Nondeterministic prompt context policy | No |
| `pdd checkup drift DEVUNIT` | Regeneration stability across repeated runs | Yes (regenerates) |

`pdd checkup coach PROMPT` (prompt coaching, Mode B) is planned; see [docs/checkup_prompt_coaching.md](checkup_prompt_coaching.md).

## Quick examples

```bash
# Lint a prompt for quality issues
pdd checkup lint prompts/refund_payment_python.prompt

# Check contract sections
pdd checkup contract check prompts/

# Build the coverage matrix
pdd checkup coverage prompts/

# Enforce waiver policy and evidence manifests
pdd checkup gate prompts/

# Verify a prompt's nondeterministic context snapshot
pdd checkup snapshot prompts/critical_python.prompt

# Check regeneration stability (uses LLM)
pdd checkup drift refund_payment
```

## CI recipe

```yaml
# .github/workflows/pdd-check.yml
steps:
  - name: Contract lint
    run: pdd checkup contract check prompts/ --strict

  - name: Coverage check
    run: pdd checkup coverage prompts/

  - name: Gate policy
    run: pdd checkup gate prompts/
```

Or as a one-liner:

```bash
pdd checkup contract check prompts/ --strict && \
pdd checkup coverage prompts/ && \
pdd checkup gate prompts/
```

## Exit codes

| Command | 0 | 1 | 2 |
|---------|---|---|---|
| `lint` | No issues | Warnings only | Errors (or warnings with `--strict`) |
| `contract check` | No issues | Warnings only | Errors (or warnings with `--strict`) |
| `coverage` | All rules covered | Unchecked rules present | Read/parse errors |
| `gate` | Policy satisfied | Policy violations | Configuration error |
| `snapshot` | Policy satisfied | Policy violations | Configuration error |
| `drift` | Stable | Unstable (API drift or test failure) | — |

## Related documentation

- [docs/contract_check.md](contract_check.md) — Contract section lint reference
- [docs/coverage_contracts.md](coverage_contracts.md) — Coverage matrix reference
- [docs/drift.md](drift.md) — Regeneration stability reference
- [docs/evidence_manifest.md](evidence_manifest.md) — Evidence manifests and gate
- [docs/prompt_lint.md](prompt_lint.md) — Prompt lint reference
- [docs/checkup_prompt_coaching.md](checkup_prompt_coaching.md) — Prompt coaching (Mode B)
