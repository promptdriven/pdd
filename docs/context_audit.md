# `pdd context-audit`

Audit token attribution by source for a hydrated prompt. Preprocesses the prompt the same way generation does and reports how many tokens each source segment contributes—without making an LLM call.

## Why this matters

PDD's context-window advantage depends on knowing exactly what is sent to the model. The prompt source file is compact, but hydration (expanding `<include>` directives, shell output, web fetches, tests, examples, and grounding) can inflate the payload significantly. Without token attribution, context rot is invisible and optimization is guesswork.

`pdd context-audit` makes the hydrated cost visible so you can:
- Detect oversized includes before they silently exceed the context limit.
- Identify the largest token consumers and target optimization effort.
- Gate CI pipelines on context budget with a configurable threshold and exit code 2.

## Requirements

- A prompt file with one or more `<include>` directives (works on any prompt).
- No LLM API key is required for deterministic portions.

## Usage

```bash
pdd context-audit <prompt_path> [OPTIONS]
```

### Arguments

| Argument | Description |
|---|---|
| `prompt_path` | Path to the prompt file to audit. |

### Options

| Option | Default | Description |
|---|---|---|
| `--model MODEL` | `PDD_MODEL_DEFAULT` env var, or `gpt-4o` | Model name used for context-limit lookup. |
| `--json` | off | Emit machine-readable JSON output instead of the human-readable table. |
| `--threshold N` | `80` | Exit with code 2 when total tokens exceed N% of the model's context limit. Set to `0` to disable. |

## Output

### Human-readable table (default)

```
Model: claude-sonnet-4-6  |  Context limit: 200 000 tokens
Total tokens: 12 450  (6.2% of context window)

Source                                   Tokens    % of total
─────────────────────────────────────────────────────────────
context/python_preamble.prompt            6 200       49.8 %
prompt_body                               3 100       24.9 %
tests/test_my_module.py                   1 800       14.5 %
examples/my_module_example.py               950        7.6 %
grounding                                   400        3.2 %  (WARN: unavailable — requires cloud)

WARN: dynamic tag <shell> detected but not expanded (nondeterministic, deferred)
```

Rows are sorted by token count descending. Deferred dynamic-tag warnings appear below the table.

### JSON output (`--json`)

```json
{
  "model": "claude-sonnet-4-6",
  "context_limit": 200000,
  "total_tokens": 12450,
  "percent_used": 6.2,
  "threshold_exceeded": false,
  "rows": [
    {"source": "context/python_preamble.prompt", "tokens": 6200, "percent": 49.8},
    {"source": "prompt_body",                    "tokens": 3100, "percent": 24.9},
    {"source": "tests/test_my_module.py",        "tokens": 1800, "percent": 14.5},
    {"source": "examples/my_module_example.py",  "tokens":  950, "percent":  7.6},
    {"source": "grounding",                      "tokens":  400, "percent":  3.2}
  ],
  "warnings": [
    "dynamic tag <shell> detected but not expanded (nondeterministic, deferred)"
  ]
}
```

## Exit codes

| Code | Meaning |
|---|---|
| `0` | Audit completed; total tokens within threshold. |
| `2` | Total tokens exceed `--threshold` percent of the context limit. |

## Grounding tokens

Cloud grounding tokens are reported as `0` with a `WARN: unavailable (requires cloud)` note when PDD Cloud is not configured. No network call is made. If you have PDD Cloud access, grounding tokens will be attributed automatically.

## Dynamic tag warnings

Tags such as `<shell>`, `<web>`, and semantic `query=` includes introduce nondeterministic content that varies by environment or time. `pdd context-audit` detects these tags in the raw source and emits a warning for each one rather than expanding them (which would require a live shell or network call). The audit counts only the deterministic portions of the payload; the actual hydrated size may be larger when dynamic tags are present.

## CI usage

```yaml
# GitHub Actions example: fail the build when context exceeds 70%
- name: Audit context budget
  run: pdd context-audit prompts/my_module_python.prompt --threshold 70
```

```bash
# Combine with --json to post results to a dashboard
pdd context-audit prompts/my_module_python.prompt --json | jq .percent_used
```

## Related commands

- [`pdd preprocess`](../README.md#5-preprocess) — expand includes and inspect the raw hydrated text.
- [`pdd replay`](../README.md#5a-replay) — reconstruct and verify a snapshot-captured expanded prompt.
- [`pdd checkup snapshot`](../README.md) — verify that prompts with nondeterministic tags have a replayable artifact.
