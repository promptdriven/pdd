# `pdd checkup` — Focused local verifier commands

`pdd checkup` exposes deterministic, fast local checks for prompt source-sets. These commands do not require an LLM (except `drift`, which regenerates to compare stability).

For the **default prompt-space experience**, use `pdd checkup prompt <target>` — a unified report that aggregates these focused checkers. See [docs/checkup_prompt.md](checkup_prompt.md). For **agentic GitHub issue/PR repair**, use `pdd checkup <issue-url>` or `pdd checkup --pr <pr-url>` (see `pdd checkup --help`).

## Mental model

```text
generate | sync | test | verify  →  action verbs (produce artifacts)
checkup prompt                    →  default prompt-space health (aggregate)
checkup lint | contract | …       →  focused deterministic checks (CI/debug)
checkup <issue-url>               →  agentic repo repair
```

## Focused verifier subcommands

| Subcommand | What it checks | LLM? |
|-----------|---------------|------|
| `pdd checkup lint <target>` | Prompt and user-story quality, vague terms, vocabulary | No (optional `--llm`) |
| `pdd checkup contract check <target>` | Contract section lint (`<contract_rules>`, `<coverage>`, waivers) | No |
| `pdd checkup coverage <target>` | Rule-to-story/test coverage matrix | No |
| `pdd checkup gate [<target>]` | Waiver policy gate, evidence manifest enforcement | No |
| `pdd checkup snapshot <prompt-file>` | Nondeterministic prompt context policy | No |
| `pdd checkup drift <devunit>` | Regeneration stability across repeated runs | Yes (regenerates) |

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

- [docs/checkup_prompt.md](checkup_prompt.md) — Unified `checkup prompt` entry point (aggregation model)
- [docs/contract_check.md](contract_check.md) — Contract section lint reference
- [docs/coverage_contracts.md](coverage_contracts.md) — Coverage matrix reference
- [docs/drift.md](drift.md) — Regeneration stability reference
- [docs/evidence_manifest.md](evidence_manifest.md) — Evidence manifests and gate
- [docs/prompt_lint.md](prompt_lint.md) — Prompt lint reference
