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

## Agentic review loop

**Fallback/mirror pass around canonical `pdd checkup --final-gate`.**

`--agentic-review-loop` is NOT a standalone adversarial review. It is a secondary,
non-authoritative mirror pass whose authority is always subordinate to the canonical
`pdd checkup --final-gate` result. The canonical gate remains the source of truth.

### When to use

Activate the agentic loop as a fallback or mirror when:
- The canonical reviewer/provider experienced an infra failure, timeout, or auth error
- The canonical gate produced malformed or empty output
- You want a non-authoritative mirror report alongside a canonical pass
- An unknown or inconclusive verdict from the canonical gate requires a secondary signal

### Adversarial framing (bounded mirror lens)

When `--adversarial-prompt` is not set, the loop substitutes the default bounded
mirror instruction:

> "Using the same criteria as canonical pdd checkup, find concrete reasons this PR
> should not merge. Do not introduce new merge criteria. Report only verifiable
> blockers or material risks."

This mirrors the same checkup criteria (correctness, source-of-truth, tests,
issue-alignment) without introducing an independent rubric. Pass `--adversarial-prompt`
explicitly to override.

### Invocation examples

```bash
# Fallback/mirror pass — no fix, report only
pdd checkup --pr https://github.com/org/repo/pull/42 \
  --agentic-review-loop --no-fix

# Mirror with fix enabled
pdd checkup --pr https://github.com/org/repo/pull/42 \
  --agentic-review-loop

# Override the default mirror lens
pdd checkup --pr https://github.com/org/repo/pull/42 \
  --agentic-review-loop \
  --adversarial-prompt "Focus only on security and data-integrity issues."
```

### Artifact status strings

The `pdd-checkup-agentic-{pr_number}.json` artifact always carries one of these
five `status` values, encoding the canonical × agentic verdict matrix:

| Status | Canonical gate | Agentic result |
|--------|---------------|----------------|
| `canonical_pass_agentic_mirror_clean` | pass | no blocking findings |
| `canonical_pass_agentic_mirror_blocking` | pass | blocking findings found |
| `canonical_unknown_agentic_fallback_pass` | absent/unknown/infra-fail | no blocking findings |
| `canonical_unknown_agentic_fallback_blocking` | absent/unknown/infra-fail | blocking findings found |
| `canonical_fail_agentic_not_authoritative` | **fail** | (any — non-authoritative) |

`canonical_fail_agentic_not_authoritative` is set whenever the upstream canonical
gate recorded a failure, regardless of what agentic reviewers found. The agentic
result is never authoritative over a canonical failure.
