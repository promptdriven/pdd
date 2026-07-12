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

### Agentic review loop (`--agentic-review-loop`)

Standalone adversarial PR checkup with dual independent reviewers, optional
bounded fixer, and a structured machine-readable verdict:

```bash
# Fix mode
# --adversarial-prompt is omitted so the safe canonical-checkup-anchored default
# lens is used ("Using the same criteria as canonical pdd checkup, find concrete
# reasons this PR should not merge. Do not introduce new merge criteria. Report
# only verifiable blockers or material risks.").
pdd checkup --pr <PR_URL> \
  --agentic-review-loop \
  --reviewers codex:/review,claude:/code-review \
  --fixer claude \
  --fresh-final-review codex \
  --max-review-rounds 5 --max-review-minutes 50 --max-review-cost 15.00 \
  --json

# Report-only mode (no file edits, commits, or pushes)
pdd checkup --pr <PR_URL> \
  --agentic-review-loop \
  --reviewers codex:/review,claude:/code-review \
  --no-fix \
  --fresh-final-review codex \
  --json
```

Emits a bounded/redacted `pdd.checkup.agentic.v1` JSON artifact containing
Layer 1 gate results, structured `findings[]`, `fix_attempts[]`,
`validation_after_fix`, `fresh_final_review`, `verdict`, and `budget` blocks.
Manual `--agentic-review-loop` writes the artifact to stdout (with `--json`) and
to an invocation-specific `./pdd-checkup-agentic-{pr_number}-{nonce}.json` path.
The exact cwd-relative public basename is included in the successful artifact's
top-level `artifact_path` field so file-based callers never guess or consume
another concurrent invocation's verdict, while absolute working-directory
components are never serialized into artifacts or retained stdout.

Hosted `pdd_cloud` integration uses the canonical final-gate command instead of
a second CLI invocation. When `PDD_CHECKUP_FALLBACK_MIRROR=1` is present,
`pdd checkup --pr <PR_URL> --issue <ISSUE_URL> --final-gate` writes the same
bounded `pdd.checkup.agentic.v1` artifact to exactly
`PDD_AGENTIC_CHECKUP_ARTIFACT_PATH`. That artifact is additive mirror/fallback
evidence; the canonical final-gate verdict remains authoritative. Hosted
Provider-native command provenance is emitted only for explicit CLI
`--reviewers role:/command` values that the review loop actually executes.
Hosted artifact-only reviewer-command metadata neither alters canonical prompts
nor appears as though an unexecuted command ran.
Exit 0 only when verdict is `pass`; non-zero for `failed`, `needs_human`,
`error`, `timeout`, or `budget_exhausted` outcomes.

The `pdd.checkup.final_gate.v1` artifact is also emitted alongside for
backwards-compatible hosted consumers.
