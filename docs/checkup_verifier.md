# PDD Checkup Verifier Namespace

`pdd checkup` is PDD's **verifier namespace**: one entry point for prompt
source-set health, focused deterministic checks, and GitHub issue/PR review.

## Prompt source-set health

Run a unified report before generating or changing code:

```bash
pdd checkup prompts/foo_python.prompt
pdd checkup prompts/
pdd checkup refund_payment
```

See [checkup_prompt_quality_gate.md](checkup_prompt_quality_gate.md) for the
automatic gate, report schema, and workflow hooks.

## Focused checks (CI / debugging)

| Command | Doc |
|---------|-----|
| `pdd checkup lint` | [prompt_lint.md](prompt_lint.md) |
| `pdd checkup contract check` | [contract_check.md](contract_check.md) |
| `pdd checkup coverage` | [coverage_contracts.md](coverage_contracts.md) |
| `pdd checkup gate` | [evidence_manifest.md](evidence_manifest.md) |
| `pdd checkup snapshot` | snapshot policy for nondeterministic tags |
| `pdd checkup drift` | [drift.md](drift.md) |

## Issue / PR checkup

```bash
pdd checkup https://github.com/org/repo/issues/123
pdd checkup --pr https://github.com/org/repo/pull/123
```

These modes are unchanged from the agentic checkup workflow.

### Agentic mirror artifact (`--agentic-review-loop`)

Fallback/mirror PR checkup for hosted consumption. Canonical `pdd checkup`
or `pdd checkup --final-gate` remains the authoritative verdict; the agentic
mirror only runs after a canonical pass or an unknown canonical infrastructure
failure (provider/parser/timeout/malformed output). It never overrides a
canonical content failure.

```bash
# Canonical final gate plus non-authoritative mirror artifact
pdd checkup --pr <PR_URL> --issue <ISSUE_URL> \
  --final-gate \
  --agentic-review-loop \
  --reviewers codex:/review,claude:/code-review \
  --adversarial-prompt "mirror canonical checkup criteria only"

# Report-only mirror around canonical PR merit review
pdd checkup --pr <PR_URL> \
  --agentic-review-loop \
  --reviewers codex:/review,claude:/code-review \
  --no-fix
```

The command emits bounded/redacted `pdd.checkup.agentic.v1` JSON to stdout
and writes the same artifact to `./pdd-checkup-agentic-{pr_number}.json`.
Stable statuses are:
`canonical_pass_agentic_mirror_clean`,
`canonical_pass_agentic_mirror_blocking`,
`canonical_unknown_agentic_fallback_pass`,
`canonical_unknown_agentic_fallback_blocking`, and
`canonical_fail_agentic_not_authoritative`.
