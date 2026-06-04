# `pdd checkup prompt`

Unified prompt-space source-set health check. Before debugging generated code, answer:
*Is this prompt clear, complete, covered, evidenced, and ready to generate from?*

## User Journey

| Step | Command | What happens |
|------|---------|--------------|
| **Check** | `pdd checkup prompt <target>` | Unified source-set report: lint, contract, coverage, waivers, evidence, snapshot/gate readiness, and recommended next steps. |
| **Explain** | `… --explain` | Read-only LLM advisory on deterministic finding IDs only. Non-fatal; does not change the exit code. |
| **Apply** | `… --interactive --apply` | Human-approved patches to `.prompt` and `user_stories/story__*.md` only. Postflight re-check runs after apply. Both flags required. |

## Usage

```bash
# Check: unified source-set health report
pdd checkup prompt prompts/refund_payment_python.prompt

# Explain: read-only advisory on findings
pdd checkup prompt refund_payment --explain

# Apply: human-approved patches (interactive terminal required)
pdd checkup prompt refund_payment --interactive --apply
```

`<target>` accepts a bare module name (`refund_payment`), a prompt filename
(`refund_payment_python.prompt`), or a path.

## Authority Model

```
Deterministic checks decide pass/fail.
--explain is optional and non-fatal.
--interactive --apply is the only write path; LLM never writes files directly.
```

- `--apply` without `--interactive` is a hard error.
- `--interactive` in a non-TTY context (CI, pipes) is a hard error.
- `--explain` alone never changes exit code.

## Aggregated Engine Checks

`pdd checkup prompt` aggregates the following deterministic engines in a single pass:

| Engine | What it checks |
|--------|---------------|
| `pdd checkup lint` | Prompt and user-story quality (vague terms, vocabulary, optional LLM review) |
| `pdd checkup contract check` | Contract-section lint (`<contract_rules>`, `<coverage>`, waivers, story `## Covers`) |
| `pdd checkup coverage` | Rule-to-story/test coverage matrix |
| `pdd checkup gate` | Evidence-manifest and waiver-policy enforcement |
| `pdd checkup snapshot` | Nondeterministic tags (`<shell>`, etc.) require replayable `.pdd/evidence` snapshots |
| Contract IR | Structured extraction of `contract_rules`, `vocabulary`, `coverage`, `waivers`, `capabilities` |

Focused checkers remain available top-level for CI and deep debugging:

```bash
pdd checkup lint <target>
pdd checkup contract check <target>
pdd checkup coverage <target>
pdd checkup gate [target]
pdd checkup snapshot <prompt_file>
pdd checkup drift <devunit>
```

## Non-Goals

- No `pdd checkup coach` subcommand — the `--explain` step is the advisory entry point.
- No `pdd checkup prompt lint` / `pdd checkup prompt gate` nesting.
- No writes in `--explain` mode.
- No non-interactive auto-apply.
- No advisory that mutates generated `src/` or policy-on-code paths (see [#1371](https://github.com/promptdriven/pdd/issues/1371)).

## Related

- [docs/prompt_lint.md](prompt_lint.md) — pre-merge prompt and user-story quality checks
- [docs/contract_check.md](contract_check.md) — deterministic contract-section lint
- [docs/coverage_contracts.md](coverage_contracts.md) — rule-to-story/test coverage matrix
- [docs/checkup_simplify.md](checkup_simplify.md) — local code candidate cleanup
