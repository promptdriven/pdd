# Prompt lint E2E demo — verifier LLM template

End-to-end test for `pdd prompt lint` and `pdd contracts` applied to a
**verifier LLM template** (`find_verification_errors_LLM.prompt`). **No
hand-authored answers, no mocks** — only the input prompt and inert fixture
inputs are written by hand. Every other artifact comes from a real `pdd`
CLI call.

## Inputs (hand-authored)

| File | Role |
|------|------|
| `prompts/find_verification_errors_LLM.prompt` | Vague verifier template (lint target) |
| `fixtures/subject_refund_python.prompt` | Subject prompt evaluated by the verifier (`--live`) |
| `fixtures/sample_program.py` | Program the verifier evaluates (`--live`) |
| `fixtures/sample_code.py` | Code module the verifier evaluates (`--live`) |
| `fixtures/sample_output.txt` | Output logs the verifier evaluates (`--live`) |

The fixtures are inputs to the verifier when it runs as an LLM call — they
are not "expected output" answer keys.

## Outputs (produced by `pdd`)

| Path | Producer |
|------|----------|
| `prompts/find_verification_errors_work_LLM.prompt` | `pdd prompt lint --ambiguity --apply` (live only) |
| `reports/lint.json` | `pdd prompt lint` |
| `reports/lint_llm_template.json` | `pdd prompt lint --llm-template` |
| `reports/contracts_check.json` | `pdd contracts check --json` |
| `reports/contracts_compile.json` | `pdd contracts compile --json` |
| `reports/formalization.json` | `pdd prompt lint --report formalization --json` |
| `reports/live.json` | `--live` summary (before/after lint + real verifier smoke) |

## Run

```bash
export PDD_SKIP_UPDATE_CHECK=1

# Deterministic CI flow (no API)
bash examples/prompt_lint_e2e_demo/demo.sh

# Full LLM chain (requires API keys, e.g. OPENAI_API_KEY)
bash examples/prompt_lint_e2e_demo/demo.sh --live

# Remove work copy
bash examples/prompt_lint_e2e_demo/demo.sh --cleanup
```

## Deterministic pipeline

1. `pdd prompt lint prompts/find_verification_errors_LLM.prompt`
2. `pdd prompt lint --llm-template prompts/find_verification_errors_LLM.prompt`
3. `pdd contracts check --json prompts/find_verification_errors_LLM.prompt`
4. `pdd contracts compile --json prompts/find_verification_errors_LLM.prompt`
5. `pdd prompt lint --report formalization --json prompts/find_verification_errors_LLM.prompt`

Success = the CLI reports the signals you would expect for a vague verifier
template: lint warnings, contract issues (missing modal verbs, vague terms),
compile errors (unstable rule IDs).

## Live pipeline

1. Copy → `prompts/find_verification_errors_work_LLM.prompt`
2. Lint the work copy (before)
3. Real verifier smoke against `fixtures/` — calls `pdd.llm_invoke` directly with
   the verifier template; records `issues_count`.
4. `pdd prompt lint --ambiguity --non-interactive --apply --json` (real LLM)
5. Lint the work copy (after) — fewer or equal warnings, `<vocabulary>` present
6. Real verifier smoke again

## Tests

```bash
# CI (no network)
pytest tests/test_prompt_lint_e2e_demo.py -q

# Opt-in: real LLM (costs money)
PDD_RUN_REAL_LLM_TESTS=1 pytest tests/test_prompt_lint_e2e_demo.py -q -m real
```

## See also

- [`docs/prompt_lint.md`](../../docs/prompt_lint.md)
- [`pdd/prompts/find_verification_errors_LLM.prompt`](../../pdd/prompts/find_verification_errors_LLM.prompt) — upstream template
- [`examples/prompt_lint_contract_e2e_demo/`](../prompt_lint_contract_e2e_demo/) — sibling demo focused on `pdd contracts` + `pdd coverage`
