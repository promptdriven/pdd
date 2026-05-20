# Prompt lint + contracts E2E demo (paired fixtures)

End-to-end test for `pdd prompt lint`, `pdd contracts`, `pdd coverage`,
`pdd generate`, and `pdd test`. **No hand-authored answers** — only the two
paired prompts and their two companion stories are written by hand. Every
other artifact is produced by running real `pdd` CLI commands.

## Why two fixtures?

The same problem domain (idempotent request handler) is written twice, so
the demo can show — deterministically, without an LLM — the contrast
between a prompt that is **not** ready to be a source of truth and one
that **is**.

| Fixture | Role | What it exercises |
|---|---|---|
| `prompts/foo_vague_python.prompt` | Negative input | vague-term warnings, missing-condition / missing-obligation compile errors, story-only / unchecked rules in coverage |
| `prompts/foo_formalized_python.prompt` | Positive input | `<vocabulary>` defines every term, every rule uses `When … MUST return … MUST [NOT] write …`, `<formalization>` block declares SMT predicates |

`pdd prompt lint --apply` (live mode, real LLM) is the migration step from
the first shape toward the second. The demo asserts the deterministic
contrast and, in `--live`, also exercises the LLM clarification pipeline
on the vague fixture.

## Inputs (hand-authored — the only files committed under prompts/ and user_stories/)

| File | Role |
|------|------|
| `prompts/foo_vague_python.prompt` | Vague contract prompt (idempotency / active user / auth) |
| `prompts/foo_formalized_python.prompt` | Same domain, source-of-truth grade (vocabulary + SMT formalization) |
| `user_stories/story__foo_vague.md` | Minimal story for the vague prompt; covers R1, R2 only |
| `user_stories/story__foo_formalized.md` | Full story for the formalized prompt; `## Glossary` + `## Covers` R1..R4 |

## Outputs (produced by `pdd`, never committed)

JSON reports:

| Path | Producer |
|------|----------|
| `reports/vague.json` | full deterministic snapshot for the vague fixture |
| `reports/formalized.json` | full deterministic snapshot for the formalized fixture |
| `reports/comparison.json` | side-by-side summary (lint, compile, coverage, formalization) |
| `reports/live.json` | `--live` summary on the vague fixture |

Persisted prompt / code / test artifacts (stable copies kept in `reports/`):

| Path | When | Source |
|------|------|--------|
| `reports/artifacts/prompt_before.prompt` | every run | copy of `prompts/foo_vague_python.prompt` |
| `reports/artifacts/prompt_after.prompt` | every run | copy of `prompts/foo_formalized_python.prompt` |
| `reports/artifacts/prompt_clarified.prompt` | `--live` | LLM-clarified work copy |
| `reports/artifacts/src/foo_work.py` | `--live` | `pdd generate` |
| `reports/artifacts/tests/test_foo_work.py` | `--live` | `pdd test --manual` |

Unified diffs between the artifacts:

| Path | When | What it shows |
|------|------|---------------|
| `reports/diffs/prompt_before_vs_after.diff` | every run | the structural migration from vague NL to source-of-truth prompt |
| `reports/diffs/prompt_before_vs_clarified.diff` | `--live` | what the LLM actually rewrote |
| `reports/diffs/prompt_clarified_vs_after.diff` | `--live` | how close the LLM landed to the formalized target |

Ephemeral mirrors used by the CLI while the demo is running (these get
cleaned up on `--cleanup` and on the end of `--live` unless `--keep-artifacts`):

| Path | Producer |
|------|----------|
| `prompts/foo_work_python.prompt` | `pdd prompt lint --ambiguity --apply` (live only) |
| `src/foo_work.py` | `pdd generate` (live only) |
| `tests/test_foo_work.py` | `pdd test --manual` (live only) |

## Run

```bash
export PDD_SKIP_UPDATE_CHECK=1

# Deterministic CI flow (no API)
bash examples/prompt_lint_contract_e2e_demo/demo.sh

# Full LLM chain on the vague fixture (requires API keys, e.g. OPENAI_API_KEY)
bash examples/prompt_lint_contract_e2e_demo/demo.sh --live

# Remove generated work copy / src / tests
bash examples/prompt_lint_contract_e2e_demo/demo.sh --cleanup
```

## Deterministic pipeline

For **each** fixture (vague, then formalized) the demo runs:

1. `pdd prompt lint <prompt>`
2. `pdd prompt lint --json <prompt>` (issue counts by code and section)
3. `pdd contracts check --json --stories user_stories <prompt>`
4. `pdd contracts compile --json <prompt>`
5. `pdd coverage --contracts --json --stories-dir user_stories --tests-dir tests <prompt>`
6. `pdd prompt lint --contracts --json --stories user_stories --tests-dir tests <prompt>`
7. `pdd prompt lint --report formalization --json <prompt>`

Then it prints a side-by-side table and writes `reports/comparison.json`.

### Expected verdict (asserted by the test suite)

| fixture | lint (warn / err) | compile (rules / oblig / errs) | coverage (checked / story_only / unchecked) | formal_issues |
|---|---|---|---|---|
| vague | ≥ 10 / 0 | 4 / ≤ 2 / ≥ 1 | 0 / 2 / ≥ 1 | ≥ 5 |
| formalized | ≤ 5 / 0 | ≥ 4 / ≥ 6 / 0 | 0 / 4 / 0 | ≤ 5 (only `FORMAL_UNBOUNDED_DOMAIN`) |

The formalized fixture intentionally keeps a small floor of
`FORMAL_UNBOUNDED_DOMAIN` warnings: that check is satisfied only by the
literal word `assume`/`bound`, which is a known sharp edge in
`formalization_lint._has_bound`. The point of the demo is the contrast in
the **other** signals (vague-term, no-observable-outcome, compile errors,
coverage status), all of which go to zero on the formalized fixture.

## Live pipeline

The vague fixture is copied into `prompts/foo_work_python.prompt` and then:

1. Lint the work copy (before)
2. `pdd prompt lint --ambiguity --non-interactive --apply --contracts --json` — real LLM rewrites in place
3. Lint the work copy (after)
4. `pdd contracts compile --json` (clarified copy)
5. `pdd coverage --contracts --json` (clarified copy)
6. `pdd generate prompts/foo_work_python.prompt --output src/foo_work.py`
7. `pdd test --manual prompts/foo_work_python.prompt src/foo_work.py --output tests/test_foo_work.py`
8. `pytest tests/test_foo_work.py`

Cleanup removes everything except the four hand-authored input files and
the demo scripts.

If every model in the fallback chain fails (rate limit, auth, unsupported
model), the demo exits with code **77** and the `@pytest.mark.real` live
test maps that to `pytest.skip(...)` instead of failing CI.

## Tests

```bash
# CI (no network)
pytest tests/test_prompt_lint_contract_e2e_demo.py -q

# Opt-in: real LLM (costs money)
PDD_RUN_REAL_LLM_TESTS=1 pytest tests/test_prompt_lint_contract_e2e_demo.py -q -m real
```

## What the pipeline does *not* yet do

`pdd prompt lint` and `pdd contracts` make a prompt precise enough that
you *could* feed its obligations to a prover; they do not themselves emit
or check a formal proof:

- no SMT/Z3 emitter (the `<formalization target="smt">` block is read but
  never solved)
- no refinement check from generated code back to obligations
- the contract IR (`pdd.contract_ir.v1`) does not express state
  invariants, quantifiers, or temporal properties — "must not corrupt
  stored state" can only be approximated by `MUST NOT write …` obligations

The formalized fixture is shaped so a future `pdd contracts prove`
command could consume its `<formalization>` blocks directly.

## See also

- [`docs/prompt_lint.md`](../../docs/prompt_lint.md)
- [`docs/contract_check.md`](../../docs/contract_check.md)
- [`docs/coverage_contracts.md`](../../docs/coverage_contracts.md)
