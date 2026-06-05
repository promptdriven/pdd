# `pdd context`

Show context-window usage by source for a hydrated prompt, rendered like Claude Code's `/context` display. Preprocesses the prompt the same way generation does and reports how many tokens each source segment contributes—without making an LLM call.

## Why this matters

PDD's context-window advantage depends on knowing exactly what is sent to the model. The prompt source file is compact, but hydration (expanding `<include>` directives, shell output, web fetches, tests, examples, and grounding) can inflate the payload significantly. Without token attribution, context rot is invisible and optimization is guesswork.

`pdd context` makes the hydrated cost visible so you can:
- Detect oversized includes before they silently exceed the context limit.
- Identify the largest token consumers and target optimization effort.
- Gate CI pipelines on context budget with a configurable threshold and exit code 2.

## Requirements

- A prompt file with one or more `<include>` directives (works on any prompt).
- No LLM API key is required for deterministic portions.

## Usage

```bash
pdd context <prompt_path> [OPTIONS]
```

### Arguments

| Argument | Description |
|---|---|
| `prompt_path` | Path to the prompt file to audit. |

### Options

| Option | Default | Description |
|---|---|---|
| `--model MODEL` | `PDD_MODEL_DEFAULT` env var, or `gpt-4o` | Model name used for context-limit lookup. |
| `--json` | off | Emit machine-readable JSON output instead of the usage box. |
| `--table` | off | Show the raw per-source token-attribution table instead of the usage box. |
| `--threshold N` | `80` | Exit with code 2 when total tokens exceed N% of the model's context limit. Set to `0` to disable. |

## Output

### Usage box (default)

```
Context Usage

  ⛁ ⛁ ⛀ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶
  ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶ ⛶
  ...

  claude-sonnet-4-6
  12,450/200,000 tokens (6.2%)

  Estimated usage by category
  ⛁ context/python_preamble.prompt: 6,200 tokens (3.1%)
  ⛀ prompt_body: 3,100 tokens (1.6%)
  ⛂ grounding: 0 tokens (0.0%)  (WARN: unavailable (requires cloud))
  ⛶ Free space: 187,550 tokens (93.8%)
```

The grid shows used context-window space split by category against free space (`⛶`). The breakdown lists one line per source. Categories are ordered largest-token-consumer first.

`pdd context` does not append the global PDD command-execution summary or core-dump notice to its output, so the default display stays equivalent to Claude Code's `/context` view.

### Per-source table (`--table`)

```
Model: claude-sonnet-4-6  |  Context limit: 200,000 tokens
Total tokens: 12,450  (6.2% of context window)

Source                                            Tokens    % of total
------------------------------------------------------------------------
context/python_preamble.prompt                     6,200         49.8%
prompt_body                                        3,100         24.9%
grounding                                              0            -  (WARN: unavailable (requires cloud))
```

Rows are sorted by token count descending. Deferred dynamic-tag warnings appear on stderr in both modes.

### JSON output (`--json`)

A single object with keys: `total_tokens`, `context_limit`, `percent_used`, `model`, `rows` (each `{source, tokens, percent}`, sorted by `tokens` descending), `warnings`, and `threshold_exceeded`.

The JSON mode writes only that JSON object to stdout, with no onboarding banner, command summary, or debug footer.

## Attribution semantics

`pdd context` attributes includes from the same expansion path used to hydrate the prompt. `lines=`, `select=`, compression modes, and nested includes are counted by their realized content, not by re-reading the whole source file. Nested includes roll up into the top-level include that brought them in; independent top-level includes each get their own row even when their text overlaps.

Missing includes are reported only when preprocess would treat the syntax as a real directive. Include and include-many examples inside code fences are left alone, and optional missing includes are skipped silently. Deferred dynamic tags (`<shell>`, `<web>`, and semantic `query=` includes) are shown as warnings and excluded from the deterministic token total.

## Exit codes

- `0`: audit completed within threshold.
- `2`: total tokens exceed `--threshold` percent of the model's context limit (useful for CI and dashboards).

## Examples

```bash
# Claude-Code /context-style usage box with default 80% threshold
pdd context prompts/my_module_python.prompt

# Raw per-source attribution table
pdd context prompts/my_module_python.prompt --table

# Audit against a specific model
pdd context prompts/my_module_python.prompt --model claude-sonnet-4-6

# JSON output for CI dashboards
pdd context prompts/my_module_python.prompt --json

# Fail CI when prompt uses more than 60% of context
pdd context prompts/my_module_python.prompt --threshold 60
```
