# `pdd checkup prompt` — Prompt source-set health report

`pdd checkup prompt <target>` is the **default prompt-space entry point** for PDD. It answers whether a prompt source-set is clear, covered, evidenced, and ready to generate from—before you debug generated code.

`<target>` may be a single `.prompt` file, a directory of prompts, or a devunit name resolved under your project layout.

## Aggregation model (not a replacement namespace)

`checkup prompt` is an **aggregate source-set report**. It calls or composes the existing deterministic checkup engines behind the scenes. It does **not** replace focused commands and does **not** nest them as subcommands.

| Layer | Command | Role |
|-------|---------|------|
| Default (prompt space) | `pdd checkup prompt <target>` | Unified health report for authors |
| Focused (CI / debug) | `pdd checkup lint`, `contract check`, `coverage`, `gate`, `snapshot`, `drift` | Canonical pass/fail for each concern |
| Heavy (repo repair) | `pdd checkup <issue-url>`, `pdd checkup --pr …` | Agentic issue/PR orchestrator |

**Authority model:**

- Deterministic checks decide pass/fail.
- Optional explanation (when implemented) is non-fatal ([#1379](https://github.com/promptdriven/pdd/issues/1379)).
- File mutation requires explicit human approval ([#1381](https://github.com/promptdriven/pdd/issues/1381)).

There is **no** `pdd checkup prompt lint`, `pdd checkup prompt gate`, or similar nesting. There are **no** aliases that redirect `pdd checkup lint` to a `prompt` subcommand.

## Status

The unified report implementation is tracked in [#1379](https://github.com/promptdriven/pdd/issues/1379). Until then, the CLI registers `pdd checkup prompt` and prints a stub message; use focused commands directly.

```bash
# Planned default experience
pdd checkup prompt prompts/refund_payment_python.prompt

# Available today (unchanged, first-class)
pdd checkup lint prompts/refund_payment_python.prompt
pdd checkup contract check prompts/
pdd checkup coverage prompts/
pdd checkup gate prompts/
pdd checkup snapshot prompts/critical_python.prompt
pdd checkup drift refund_payment
```

## Related documentation

- [docs/checkup_verifier.md](checkup_verifier.md) — Focused local verifier commands and CI recipe
- [docs/contract_check.md](contract_check.md) — Contract section lint
- [docs/coverage_contracts.md](coverage_contracts.md) — Coverage matrix
- [docs/prompt_lint.md](prompt_lint.md) — Prompt lint
- [docs/drift.md](drift.md) — Regeneration stability
- [docs/evidence_manifest.md](evidence_manifest.md) — Evidence manifests and gate
