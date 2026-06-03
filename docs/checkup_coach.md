# `pdd checkup coach`

Schema-aware prompt coaching: bounded, read-only analysis of a `.prompt` file and
its linked stories against the `pdd.prompt_contract_ir.v1` IR schema
(`contract_rules`, `vocabulary`, `coverage`, `waivers`, `capabilities`, stories, tests).

Deterministic analysis always runs. An optional LLM pass produces schema-shaped
improvement suggestions. No file writes — all output is advisory.

## Usage

```bash
# Deterministic coaching only (no LLM)
pdd checkup coach prompts/my_feature_python.prompt

# With LLM suggestions
pdd checkup coach prompts/my_feature_python.prompt --llm

# Machine-readable output
pdd checkup coach prompts/my_feature_python.prompt --json

# Custom stories directory
pdd checkup coach prompts/my_feature_python.prompt --stories user_stories/

# Combined
pdd checkup coach prompts/my_feature_python.prompt --llm --stories user_stories/ --json
```

## What it checks

The coaching pipeline runs in order:

1. **Lint** (`pdd checkup lint`) — vague terms, missing observable outcomes
2. **Contract check** (`pdd checkup contract check`) — rule ID validity, modal verbs, waiver integrity
3. **Coverage** (`pdd checkup coverage`) — rule-to-story/test/waiver matrix gaps
4. **IR parse** — extracts the `pdd.prompt_contract_ir.v1` structured representation
5. **Bounded evidence gather** — reads linked stories, tests, and local files (max depth/files; no network or exec)
6. **LLM coaching pass** (`--llm` only) — schema-shaped suggestions via `checkup_coach_LLM.prompt`
7. **Output** — human-readable coaching cards + optional JSON (`pdd.prompt_coaching.v1`)

## Output

### Human-readable (default)

Suggestions are grouped by section (`contract_rules`, `vocabulary`, `coverage`, `capabilities`, stories):

```
Coaching: prompts/my_feature_python.prompt

[R2] vocabulary gap
  Term "remaining refundable amount" is used in R2 but has no <vocabulary> entry.
  Suggestion: add a definition to disambiguate from "refundable amount" in R1.

[coverage] unchecked rule
  R4 (Idempotency) has no story, test, or waiver in <coverage>.
  Suggestion: add story__refund_idempotency.md and link it under R4.

2 suggestion(s), 0 lint error(s), 1 lint warning(s), 1 coverage gap(s)
```

### JSON (`--json`)

Emits a `PromptCoachingReport` object (`pdd.prompt_coaching.v1`):

```json
{
  "schema_version": "pdd.prompt_coaching.v1",
  "prompt_path": "prompts/my_feature_python.prompt",
  "llm_model": "claude-sonnet-4-6",
  "suggestions": [
    {
      "rule_id": "R2",
      "section": "vocabulary",
      "finding": "vocabulary gap",
      "suggestion": "Add a <vocabulary> entry for 'remaining refundable amount'.",
      "evidence_refs": ["user_stories/story__refund_over_remaining.md"]
    }
  ],
  "evidence_files": ["user_stories/story__refund_over_remaining.md"],
  "lint_warn_count": 1,
  "lint_error_count": 0,
  "contract_warn_count": 0,
  "contract_error_count": 0,
  "coverage_gaps": ["R4"]
}
```

`llm_model` is `null` when `--llm` is not passed or the LLM is unavailable.

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | No errors (warnings may be present) |
| `1` | One or more deterministic errors |

LLM failure never changes the exit code set by the deterministic checks. Use `--strict` to promote warnings to errors.

## Options

| Option | Description |
|--------|-------------|
| `PROMPT` | Path to the `.prompt` file to coach (required) |
| `--llm` | Enable the LLM coaching pass for schema-shaped suggestions |
| `--stories DIR` | Directory to scan for linked `story__*.md` files (default: `user_stories/`) |
| `--tests DIR` | Directory to scan for test evidence (default: `tests/`) |
| `--json` | Machine-readable JSON output (`pdd.prompt_coaching.v1`) |
| `--strict` | Promote warnings to errors for deterministic checks |

## Non-goals

- Does not write or apply suggested changes (write-layer follow-up).
- Does not run `pdd generate` or `pdd sync`.
- Does not perform `checkup policy check` (see issues #1370, #1371 for effect IR and capability policy).
- Does not launch a full GitHub-issue agentic checkup.

## Relationship to other checkup subcommands

| Subcommand | Purpose |
|------------|---------|
| `pdd checkup lint` | Fast vague-term heuristic scan |
| `pdd checkup contract check` | Deterministic contract-section lint |
| `pdd checkup coverage` | Rule-to-story/test coverage matrix |
| **`pdd checkup coach`** | **Combined pipeline + optional LLM suggestions** |

`checkup coach` reuses the same deterministic engines as the three commands above and adds LLM-powered schema-shaped suggestions on top. Use the individual subcommands in CI for fast gates; use `coach` interactively during prompt authoring to get improvement hints.

## Demo

An example script will be available at `examples/checkup_coach_example.py` after the module is generated.
