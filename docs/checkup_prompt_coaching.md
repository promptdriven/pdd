# `pdd checkup` — Prompt Coaching (Mode B)

Prompt coaching is the **incremental authoring loop** for improving prompts against the PDD contract schema. It is distinct from:

- **Mode A — Local verifier** (`pdd checkup lint`, `contract check`, `coverage`, etc.): inspects existing artifacts deterministically. See [docs/checkup_verifier.md](checkup_verifier.md).
- **Mode C — Agentic repo repair** (`pdd checkup <issue-url>`): runs the full 8-step orchestrator to resolve a GitHub issue.

Prompt coaching (Mode B) targets the inner loop of prompt authoring: after you write or revise a prompt, `coach` walks through each contract-schema section, flags issues, and suggests targeted improvements without regenerating code.

## `pdd checkup coach` (planned)

```bash
pdd checkup coach prompts/refund_payment_python.prompt
```

> **Note:** `checkup coach` is not yet implemented. This document describes the planned interaction model. The implementation is tracked in the epic #833 stack (follow-up issues #1379–#1381).

## Schema sections the coach reviews

The coaching loop maps to the same contract-schema sections as `pdd checkup contract check`:

| Section | What coaching checks |
|---------|---------------------|
| `<contract_rules>` | Modal verbs, stable IDs, observable behavior, missing MUST/MUST NOT |
| `<vocabulary>` | Covers all vague terms flagged by lint, no circular definitions |
| `<capabilities>` | MAY/MUST NOT side-effect declarations are explicit |
| `<non_responsibilities>` | Out-of-scope items are listed |
| `<coverage>` | Each rule has a story, test, waiver, or explicit TODO |
| `<waivers>` | Valid fields, non-expired, reference existing rule IDs |

## The coaching authoring loop

1. **Write or revise** your prompt's contract sections.
2. **Run `pdd checkup lint`** — catches vague terms and structural issues (deterministic).
3. **Run `pdd checkup contract check`** — validates rule IDs, modal verbs, and coverage references.
4. **Run `pdd checkup coverage`** — shows the rule-to-story/test matrix.
5. **(Planned) Run `pdd checkup coach`** — LLM-assisted per-section suggestions.
6. **Iterate** on `contract_rules`, `vocabulary`, and `coverage` until checks pass.
7. **Run `pdd checkup gate`** — verifies waiver policy.

Steps 2–4 and 7 are fast, deterministic, and CI-safe. Step 5 uses an LLM and is intended for interactive use during prompt authoring.

## Coach vs. issue-url checkup

| | `pdd checkup coach PROMPT` | `pdd checkup <issue-url>` |
|--|---------------------------|--------------------------|
| **Input** | A single `.prompt` file | A GitHub issue URL |
| **Output** | Per-section improvement suggestions | PR with code changes |
| **LLM use** | Targeted, prompt-authoring scope | Full 8-step orchestrator |
| **Scope** | Prompt quality only | Codebase repair |
| **When to use** | While writing or revising a prompt | After an issue is filed |

## Related documentation

- [docs/checkup_verifier.md](checkup_verifier.md) — Local verifier namespace (Mode A)
- [docs/contract_check.md](contract_check.md) — Contract section lint reference
- [docs/coverage_contracts.md](coverage_contracts.md) — Coverage matrix reference
- [docs/prompting_guide.md](prompting_guide.md) — Contract rules, vocabulary, waivers authoring guide
